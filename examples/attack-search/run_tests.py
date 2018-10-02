from os import listdir
from os.path import isfile, join
from subprocess import Popen, PIPE

automatic_path = "./automatic/"
automatic  = [f for f in listdir(automatic_path) if isfile(join(automatic_path, f))]
automatic.sort()


# Set for timeout in seconds
t = 100

for h in ["1","2"]:
    print("\n\nAnalyzing files from './automatic/ with heuristic " + h + ":\n")
    for a in automatic:
        p = Popen(["../../search.native", h, automatic_path + a], stdin=PIPE, stdout=PIPE, stderr=PIPE)
        if len(a) < 15:
            a = a + "\t"
        try:
            output, err = p.communicate(timeout = t)
        except:
            p.kill()
            print('\033[95m' + a + '\033[93m' + "\tTimeout     time: > " + str(t) + " s" + '\033[0m')
            continue

        found = "false"
        lines = output.splitlines()
        for i in range(len(lines)):
            l = lines[i]
            if b"Found attack:" in l:
                found = l[14:]
                time = lines[i+1][10:]
                break
        if found == b"true":
            print('\033[95m' + a + '\033[92m' + "\tFound!      time: " + str(time)[2:-1] + '\033[0m')
        else:
            print('\033[95m' + a + '\033[91m' + "\tNot found   time: " + str(time)[2:-1] + '\033[0m')
