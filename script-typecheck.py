import subprocess

subprocess.run(["python", "-m", "mypy", "rfb_mc"], check=True)
