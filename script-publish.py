import subprocess

subprocess.run(["python", "script-test.py"])

subprocess.run(["python", "script-build.py"])

subprocess.run(["python", "-m", "pip", "install", "twine"])

subprocess.run(["python", "-m", "twine", "upload", "--repository", "pypi", "dist/*"])
