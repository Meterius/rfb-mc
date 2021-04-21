from ast import literal_eval
from collections import Counter
from decimal import Decimal
from operator import itemgetter
from typing import TypedDict, Optional, Literal, Dict, Any, Iterable, Tuple, List
import uuid

from rfb_mc.restrictive_formula_module import get_restrictive_formula_module
from rfb_mc.store import StoreBase, StoreData
from rfb_mc.types import RfBmcTask, RfBmcResult, Params


def v1_encode_rf_bmc_task(task: RfBmcTask) -> str:
    return repr((
        task.rfm_guid,
        get_restrictive_formula_module(task.rfm_guid).encode_restrictive_formula_params(
            task.rfm_formula_params,
        ),
        task.a,
        task.q
    ))


def v1_decode_rf_bmc_task(task: str) -> RfBmcTask:
    rfm_guid, rfm_formula_params, a, q = literal_eval(task)

    return RfBmcTask(
        rfm_guid=rfm_guid,
        rfm_formula_params=get_restrictive_formula_module(rfm_guid).decode_restrictive_formula_params(
            rfm_formula_params,
        ),
        a=a,
        q=q
    )


def v1_encode_rf_bmc_result(result: RfBmcResult) -> str:
    return repr(tuple(result))


def v1_decode_rf_bmc_result(result: str) -> RfBmcResult:
    return RfBmcResult(*literal_eval(result))


def v1_encode_rf_bmc_task_result(task_result: Tuple[RfBmcTask, RfBmcResult]) -> str:
    return repr((
        v1_encode_rf_bmc_task(task_result[0]),
        v1_encode_rf_bmc_result(task_result[1])
    ))


def v1_decode_rf_bmc_task_result(task_result: str) -> Tuple[RfBmcTask, RfBmcResult]:
    task, result = literal_eval(task_result)

    return (
        v1_decode_rf_bmc_task(task),
        v1_decode_rf_bmc_result(result),
    )


DynamodbV1RfBmcResultsMap = Dict[str, Decimal]


def v1_encode_rf_bmc_results_map(
    rf_bmc_results_map: Dict[RfBmcTask, Counter[RfBmcResult]],
) -> DynamodbV1RfBmcResultsMap:
    return {
        v1_encode_rf_bmc_task_result((task, result)): Decimal(rf_bmc_results_map[task][result])
        for task in rf_bmc_results_map
        for result in rf_bmc_results_map[task]
    }


def v1_decode_rf_bmc_results_map(
    rf_bmc_results_map: DynamodbV1RfBmcResultsMap,
) -> Dict[RfBmcTask, Counter[RfBmcResult]]:
    task_results = list(map(v1_decode_rf_bmc_task_result, rf_bmc_results_map.keys()))

    tasks = set(map(itemgetter(0), task_results))

    return {
        task: Counter({
            result: int(rf_bmc_results_map[v1_encode_rf_bmc_task_result((task, result))])
            for result in [task_result[1] for task_result in task_results if task_result[0] == task]
        })
        for task in tasks
    }


class DynamodbV1Params(TypedDict):
    bit_width_counter: Dict[str, Decimal]


def v1_encode_params(params: Params) -> DynamodbV1Params:
    return {
        "bit_width_counter": {
            str(key): Decimal(params.bit_width_counter[key])
            for key in params.bit_width_counter.keys()
        }
    }


def v1_decode_params(params: DynamodbV1Params) -> Params:
    return Params(
        bit_width_counter=Counter({
            int(key): int(params["bit_width_counter"][key])
            for key in params["bit_width_counter"]
        })
    )


class DynamodbV1StoreData(TypedDict):
    id: str
    version: Literal[1]
    params: DynamodbV1Params
    rf_bmc_results_map: DynamodbV1RfBmcResultsMap


def v1_encode_store_data(ident: str, data: StoreData) -> DynamodbV1StoreData:
    return DynamodbV1StoreData(
        id=ident,
        version=1,
        params=v1_encode_params(data.params),
        rf_bmc_results_map=v1_encode_rf_bmc_results_map(
            data.rf_bmc_results_map,
        )
    )


def v1_decode_store_data(data: DynamodbV1StoreData) -> StoreData:
    return StoreData(
        params=v1_decode_params(data["params"]),
        rf_bmc_results_map=v1_decode_rf_bmc_results_map(data["rf_bmc_results_map"])
    )


def decode_store_data(item: Any) -> Tuple[int, StoreData]:
    """
    Decodes a database item of any known version,
    returns the version it was encoded in and the interpreted store data
    """

    if item["version"] == 1:
        typed_item: DynamodbV1StoreData = item
        return item["version"], v1_decode_store_data(typed_item)
    else:
        raise ValueError(f"Unexpected version \"{item['version']}\" in store data entry")


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
        data = self.get_store_data_entry(self.table, self.ident)

        with self.data_lock:
            self.data = data

    def _add_rf_bmc_results(self, task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]]):
        task_results = list(task_results)

        # if no results are available only the synchronization needs to be performed
        if len(task_results) == 0:
            self.sync()
            return

        # update expression will increment and create the necessary counters

        task_results_increments = Counter(task_results)

        update_expression_set: List[str] = []
        update_expression_add: List[str] = []

        expression_attribute_names = {}
        expression_attribute_values = {
            ":version": DynamodbStore.VERSION,
        }

        for idx, task_result in enumerate(task_results):
            update_expression_add.append(
                f"rf_bmc_results_map.#task_result_{idx} :inc_task_result_{idx}"
            )

            expression_attribute_values[f":inc_task_result_{idx}"] = task_results_increments[task_result]
            expression_attribute_names[f"#task_result_{idx}"] = v1_encode_rf_bmc_task_result(task_result)

        update_expression = "".join([
            "SET " + ", ".join(update_expression_set) + " " if update_expression_set else "",
            "ADD " + ", ".join(update_expression_add) + " " if update_expression_add else "",
        ])

        # increments the necessary counters and retrieves the previous store data that was stored
        response = self.table.update_item(
            Key={"id": self.ident},
            UpdateExpression=update_expression,
            ConditionExpression="attribute_exists(id) AND version = :version",
            ExpressionAttributeValues=expression_attribute_values,
            ExpressionAttributeNames=expression_attribute_names,
            ReturnValues="ALL_OLD"
        )

        # data object that was previously stored in the data entry before increment updates where performed
        data = decode_store_data(response["Attributes"])[1]

        # update the store data according to database updates
        for task, result in task_results:
            if task not in data.rf_bmc_results_map:
                data.rf_bmc_results_map[task] = Counter[RfBmcResult]()

            data.rf_bmc_results_map[task][result] += 1

        # write the synchronized update back to memory
        with self.data_lock:
            self.data = data

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

        item: Any = table.get_item(
            Key={
                "id": ident,
            }
        )["Item"]

        return decode_store_data(item)

    @staticmethod
    def replace_store_data_entry(
        table,
        ident: str,
        store: StoreData,
    ):
        """
        Removes the store entry and then puts the provided data in the entry.
        """

        table.delete_item(
            Key={
                "id": ident,
            },
        )

        item: DynamodbV1StoreData = v1_encode_store_data(ident, store)

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

        item: DynamodbV1StoreData = DynamodbV1StoreData(
            id=ident,
            version=1,
            params=v1_encode_params(params),
            rf_bmc_results_map={},
        )

        try:
            table.put_item(
                Item=item,
                ConditionExpression="attribute_not_exists(id)",
            )
        except table.meta.client.exceptions.ConditionalCheckFailedException as err:
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
