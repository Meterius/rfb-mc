import shutil
import subprocess
import os

subprocess.run(["python", "-m", "pip", "install", "twine", "build"])

if os.path.exists("dist"):
    shutil.rmtree("dist")

if os.path.exists("build"):
    shutil.rmtree("build")

if os.path.exists("rfb_mc.egg-info"):
    shutil.rmtree("rfb_mc.egg-info")

subprocess.run(["python", "-m", "build"])

subprocess.run(["python", "-m", "twine", "upload", "--repository", "pypi", "dist/*"])

