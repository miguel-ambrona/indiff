from os import listdir
from os.path import isfile, join
from subprocess import Popen, PIPE

attacks_path = "./attacks/"
mustfail_path = "./must-fail/"

attacks  = [f for f in listdir(attacks_path) if isfile(join(attacks_path, f))]
mustfail = [f for f in listdir(mustfail_path) if isfile(join(mustfail_path, f))]

attacks.sort()
mustfail.sort()

print "\nAnalyzing files from './attacks/:\n"

for a in attacks:
    p = Popen(["../../test.native", attacks_path + a], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    output, err = p.communicate()
    time = ""
    for l in output.splitlines():
        if "Solved in" in l:  time = l[10:-3] + "\tms"
    if "There does not exist a simulator for the distinguisher" in output:
        print( '{:<40s} {:<16s} {:<30s}'.format('\033[95m' + a,\
                                                '\033[92m' + "\tValid" + '\033[0m', time))
    else:
        print( '{:<40s} {:<16s} {:<30s}'.format('\033[93m' + a,\
                                                '\033[91m' + "\tFail" + '\033[0m', time))

print "\n\nAnalyzing files from './must-fail/:\n"

for a in mustfail:
    p = Popen(["../../test.native", mustfail_path + a], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    output, err = p.communicate()
    time = ""
    for l in output.splitlines():
        if "Solved in" in l:  time = l[10:-3] + "\tms"
    if "The following assignment represents a valid simulator for the distinguisher" in output:
        print( '{:<40s} {:<16s} {:<20s}'.format('\033[95m' + a,\
                                                '\033[92m' + "\tInvalid" + '\033[0m', time))
    else:
        print( '{:<40s} {:<16s} {:<20s}'.format('\033[93m' + a,\
                                                '\033[91m' + "\tFail" + '\033[0m', time))

print ""
