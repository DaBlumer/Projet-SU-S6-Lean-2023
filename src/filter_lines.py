

from sys import argv


f = open(argv[1], 'r')
lines = f.read().split('\n')
f.close()

filter = [(int(i[0])-1, int(i[1])) for i in (j.split('-') for j in argv[2].split(';'))]

out = open(argv[1], 'w')

for rng in filter:
    for i in range(rng[0], rng[1]):
        out.write(lines[i])
        out.write('\n')
out.close()


# base sous_groupes ordre morphismes quotient theoremes_isomorphisme
