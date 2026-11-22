import csv,sys,statistics as st,glob
for f in sorted(glob.glob('*.csv')):
    if f=='fid.csv': continue
    rows=list(csv.reader(open(f)))
    if not rows: continue
    to=sum(r[1]=='124' for r in rows); fin=[r for r in rows if r[1] in('10','20')]
    other=len(rows)-to-len(fin)
    def col(i): return [int(r[i] or 0) for r in fin]
    def nz(i): return 100*sum(x>0 for x in col(i))//max(len(fin),1)
    def med(i): return int(st.median(col(i))) if fin else 0
    t=[float(r[2]) for r in fin]
    print("%-12s to=%3d err=%d maxT=%5.1f sumT=%6.0f | confl med %6d | restarts nz%3d%% med %5d | deps nz%3d%% | depresets nz%3d%% med %4d | reductions nz%3d%% med %4d | coll nz%3d%% med %4d | reloc nz%3d%%"%(f[:-4],to,other,max(t) if t else 0,sum(t),med(3),nz(4),med(4),nz(5),nz(6),med(6),nz(7),med(7),nz(8),med(8),nz(9)))
