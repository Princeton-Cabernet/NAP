import os
import time
import sys
from stat import S_ISREG, ST_CTIME, ST_MODE
from pathlib import Path


def create_namelist(dir_path):

    paths = sorted(Path(dir_path).iterdir(), key=os.path.getmtime)
    for p in paths:
        print(p)

create_namelist(sys.argv[1])
