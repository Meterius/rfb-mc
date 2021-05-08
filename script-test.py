import subprocess

subprocess.run(["python", "-m", "unittest", "discover", "rfb_mc/test"], check=True)
