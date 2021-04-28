import os
import shutil
import subprocess

if os.path.exists("dist"):
    shutil.rmtree("dist")

if os.path.exists("build"):
    shutil.rmtree("build")

if os.path.exists("rfb_mc.egg-info"):
    shutil.rmtree("rfb_mc.egg-info")

subprocess.run(["python", "-m", "pip", "install", "build"])

subprocess.run(["python", "-m", "build"])
