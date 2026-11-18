from math import comb
from itertools import combinations
n=4; cube=list(range(1<<n))
for K in range(2,n+1):
    s=sum(comb(n-1,j) for j in range(K-1))
    crit=(n-1)*comb(n-2,K-2)>=s
    tail=[a for a in cube if a.bit_count()>=K]
    low=sorted(set(cube)-set(tail))
    count=0;fails=0
    for flags in range(1<<len(low)):
        F=set(tail)|{a for j,a in enumerate(low) if flags>>j&1}
        if any(a|b not in F for a,b in combinations(F,2)):continue
        count+=1
        fails+=sum(2*a.bit_count()-n for a in F)<0
    assert crit==(fails==0)
    print(K,count,fails)
