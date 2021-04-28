import setuptools

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setuptools.setup(
    name="rfb_mc",
    version="0.0.8",
    author="Jonah Leander Hoff",
    author_email="jonah-hoff@outlook.com",
    description="Performs model counting using restrictive formulas",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/Meterius/rfb-mc",
    project_urls={
        "Bug Tracker": "https://github.com/Meterius/rfb-mc/issues",
    },
    packages=setuptools.find_packages(exclude=["*.tests", "*.tests.*", "tests.*", "tests"]),
    include_package_data=True,
    python_requires=">=3.6",
)