from decimal import Decimal
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from typing import Optional, Iterable, Tuple, TypedDict
import uuid
from rfb_mc.serialization import SerializedV1StoreData, v1_encode_rf_bmc_task_result, decode_store_data, \
    v1_encode_store_data, v1_encode_params, v1_encode_bmc_task_result
from rfb_mc.store import StoreBase, StoreData
from rfb_mc.types import RfBmcTask, RfBmcResult, Params, BmcTask, BmcResult


class DynamodbV1StoreItemBmcTask(TypedDict):
    a: Decimal


class DynamodbV1StoreItemBmcResult(TypedDict):
    bmc: Optional[Decimal]


class DynamodbV1StoreItemBmcTaskResult(TypedDict):
    task: DynamodbV1StoreItemBmcTask
    result: DynamodbV1StoreItemBmcResult


def v1_convert_dynamodb_store_item_bmc_task_result(
    task_result: DynamodbV1StoreItemBmcTaskResult,
) -> Tuple[BmcTask, BmcResult]:
    return BmcTask(
        a=int(task_result["task"]["a"]),
    ), BmcResult(
        bmc=int(task_result["result"]["bmc"]),
    )


def v1_convert_bmc_task_result(
    task_result: Tuple[BmcTask, BmcResult],
) -> DynamodbV1StoreItemBmcTaskResult:
    return DynamodbV1StoreItemBmcTaskResult(
        task=DynamodbV1StoreItemBmcTask(
            a=Decimal(task_result[0].a),
        ),
        result=DynamodbV1StoreItemBmcResult(
            bmc=Decimal(task_result[1].bmc),
        )
    )


class DynamodbV1StoreItem(SerializedV1StoreData):
    id: str
    bmc_task_result: Optional[DynamodbV1StoreItemBmcTaskResult]


def v1_convert_dynamodb_store_item(item: DynamodbV1StoreItem) -> SerializedV1StoreData:
    return SerializedV1StoreData(
        version=1,
        params=item["params"],
        rf_bmc_results_map=item["rf_bmc_results_map"],
        bmc_task_result=v1_encode_bmc_task_result(
            v1_convert_dynamodb_store_item_bmc_task_result(item["bmc_task_result"])
        ) if item["bmc_task_result"] is not None else None,
    )


def v1_convert_store_data(store_data: StoreData) -> DynamodbV1StoreItem:
    return DynamodbV1StoreItem(
        **v1_encode_store_data(store_data),
        bmc_task_result=v1_convert_bmc_task_result(store_data.bmc_task_result)
        if store_data.bmc_task_result is not None else None
    )


class DynamodbStore(StoreBase):
    VERSION = 1

    def __init__(self, table, ident: str):
        """
        Initializes a dynamodb store, requires the identifier to point to
        an existing store data entry. It modifies the data format if the version is
        different as otherwise update methods will throw.
        """

        super().__init__(
            DynamodbStore.get_and_correct_store_data_entry(table, ident)
        )

        self.table = table
        self.ident = ident

    def sync(self):
        data = self.get_store_data_entry(self.table, self.ident)[1]

        with self.data_lock:
            self.data = data

    def _add_results(
        self,
        bmc_task_result: Optional[Tuple[BmcTask, BmcResult]],
        rf_bmc_task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]],
    ):
        # dynamodb request to increment rf bmc task result counters

        def send_rf_bmc_request(
            task_result: Tuple[RfBmcTask, RfBmcResult],
            count: int,
        ):
            expression_attribute_names = {
                "#task_result": v1_encode_rf_bmc_task_result(task_result),
            }

            expression_attribute_values = {
                ":version": DynamodbStore.VERSION,
                ":inc": count,
            }

            update_expression = "ADD rf_bmc_results_map.#task_result :inc"

            # increments the necessary counters
            return self.table.update_item(
                Key={"id": self.ident},
                UpdateExpression=update_expression,
                ConditionExpression="attribute_exists(id) AND version = :version",
                ExpressionAttributeValues=expression_attribute_values,
                ExpressionAttributeNames=expression_attribute_names,
            )

        # dynamodb request to update the bmc task result

        def send_bmc_request(task_result: Tuple[BmcTask, BmcResult]):
            dyn_task_result = v1_convert_bmc_task_result(task_result)

            try:
                # applies the bmc task result
                return self.table.update_item(
                    Key={"id": self.ident},
                    UpdateExpression="SET bmc_task_result = :bmc_task_result",
                    ConditionExpression="attribute_exists(id) AND version = :version AND "
                                        "(attribute_not_exists(bmc_task_result) "
                                        "OR bmc_task_result = :null "
                                        "OR bmc_task_result.task.a <= :bmc_task_a)",
                    ExpressionAttributeValues={
                        ":null": None,
                        ":version": DynamodbStore.VERSION,
                        ":bmc_task_result": dyn_task_result,
                        ":bmc_task_a": dyn_task_result["task"]["a"],
                    },
                )
            except self.table.meta.client.exceptions.ConditionalCheckFailedException:
                return None

        with ThreadPoolExecutor() as executor:
            rf_bmc_task_result_counter = Counter(rf_bmc_task_results)

            fs = []

            if bmc_task_result:
                fs.append(executor.submit(send_bmc_request, bmc_task_result))

            for task_result in rf_bmc_task_result_counter:
                fs.append(executor.submit(send_rf_bmc_request, task_result, rf_bmc_task_result_counter[task_result]))

            for fut in fs:
                fut.result()

        self.sync()

    @classmethod
    def get_and_correct_store_data_entry(
        cls,
        table,
        ident: str,
    ) -> StoreData:
        """
        Retrieves the store data and updates the data format if the version is
        different.
        """

        version, data = DynamodbStore.get_store_data_entry(table, ident)

        # ensures the data format is correct in order for class method to
        # update the data correctly
        if version != cls.VERSION:
            cls.replace_store_data_entry(table, ident, data)

        return data

    @staticmethod
    def get_store_data_entry(
        table,
        ident: str,
    ) -> (int, StoreData):
        """
        Retrieves the store data entry with the given identifier from
        the table and decodes it.
        """

        item: DynamodbV1StoreItem = table.get_item(
            Key={
                "id": ident,
            }
        )["Item"]

        return decode_store_data(v1_convert_dynamodb_store_item(item))

    @staticmethod
    def replace_store_data_entry(
        table,
        ident: str,
        store_data: StoreData,
    ):
        """
        Removes the store entry and then puts the provided data in the entry.
        """

        table.delete_item(
            Key={
                "id": ident,
            },
        )

        item: DynamodbV1StoreItem = v1_convert_store_data(store_data)

        table.put_item(
            Item=item
        )

    @staticmethod
    def create_store_data_entry(
        table,
        params: Params,
        ident: Optional[str] = None,
        accept_existing: bool = False,
    ) -> str:
        """
        Creates an empty store entry.
        If the ident is specified it will be used, otherwise a uuid4 id will be generated.
        If accept_existing is True and the ident is specified it will not raise an error if there already
        exist a store entry with the given ident.
        Note that if ident is not specified, this method will retry until an ident is generated that does not already
        exist.
        """

        ident_specified = ident is not None
        # a generated uuid4 id is highly unlikely to collide with existing ids
        ident = ident if ident_specified else str(uuid.uuid4())

        item: DynamodbV1StoreItem = DynamodbV1StoreItem(
            id=ident,
            version=1,
            params=v1_encode_params(params),
            rf_bmc_results_map={},
            bmc_task_result=None,
        )

        try:
            table.put_item(
                Item=item,
                ConditionExpression="attribute_not_exists(id)",
            )
        except table.meta.client.exceptions.ConditionalCheckFailedException:
            if ident_specified:
                if accept_existing:
                    return ident
                else:
                    raise RuntimeError(f"Store entry with ident \"{ident}\" already exists")
            else:
                # retry creating a store entry since the id was already generated before
                return DynamodbStore.create_store_data_entry(
                    table, params, None, accept_existing
                )

        return ident
