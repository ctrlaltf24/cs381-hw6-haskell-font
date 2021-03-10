import glob
import string
print("letters=[(Define \"Letter \" [] [])",end='')
for file in sorted(glob.glob("letters_clean/*")):
    f = open(file)
    first_line=""
    print(",(Define \"Letter"+file[14:15]+"\" [\"x\",\"y\"] [(Pen Up)",end='')
    for line in f:
        line=line[:len(line)-1]
        if(line=="(plate" or line==")"):
            continue
        line=line[3:-1]
        if(line=="z"):
            line=first_line
            line_x=int(line[:line.find(" ")])
            line_y=int(line[line.find(" ")+1:])
            line_x=int(line_x/5)
            line_y=int(line_y/5)
            line_y=-1*(int(line_y)-800)
            print(",(Move (Add (Lit",line_x,") (Ref \"x\")) (Add (Lit",line_y,") (Ref \"y\")))",end='')
            print(",(Pen Up)",end='')
            first_line=""
            continue
        line = line[2:]
        line_x=int(line[:line.find(" ")])
        line_y=int(line[line.find(" ")+1:])
        line_x=int(line_x/5)
        line_y=int(line_y/5)
        line_y=-1*(line_y-800)
        print(",(Move (Add (Lit",line_x,") (Ref \"x\")) (Add (Lit",line_y,") (Ref \"y\")))",end='')
        if(first_line==""):
            first_line=line
            print(",(Pen Down)",end='')
    print("])",end='')
print(']')