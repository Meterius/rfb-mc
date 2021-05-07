import subprocess

subprocess.run(["python", "script-test.py"], check=True)

subprocess.run(["python", "script-build.py"], check=True)

subprocess.run(["python", "-m", "pip", "install", "twine"], check=True)

subprocess.run(["python", "-m", "twine", "upload", "--repository", "pypi", "dist/*"], check=True)
