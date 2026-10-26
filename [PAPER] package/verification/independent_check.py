"""Exhaustive definition-level check for all 32,766 binary words of lengths 1-14.
Supporting finite check; the arbitrary-length result is proved in the manuscript.
Uses only the Python standard library. Run: python independent_check.py
"""
from pathlib import Path
import json
log=""
def rotations(mask,n):
    full=(1<<n)-1
    return {((mask>>r)|(mask<<(n-r)))&full for r in range(n)}

rows=[]
total=0
for n in range(1,15):
    expected=set()
    if n%2:
        for mask in (0,(1<<n)-1,1,((1<<n)-1)^1):
            expected.update(rotations(mask,n))
    else:
        for k in range(1,n,2):
            expected.update(rotations((1<<k)-1,n))
        if n%4==2:
            expected.update(rotations(sum(1<<i for i in range(0,n,2)),n))
    extremal=set()
    smallest=None
    bound=(n-1)//2
    masks=[((1<<m)-1,(1<<(2*m))-1,m) for m in range(1,n//2+1)]
    for w in range(1<<n):
        doubled=w|(w<<n)
        squares=set()
        for i in range(n):
            rotation=doubled>>i
            for half_mask,whole_mask,m in masks:
                block=rotation&whole_mask
                if (block&half_mask).bit_count()==(block>>m).bit_count():
                    squares.add((m,block))
        count=len(squares)
        assert count>=bound,(n,w,count,bound)
        if count==bound:
            extremal.add(w)
        smallest=count if smallest is None else min(smallest,count)
    assert extremal==expected,(n,sorted(extremal^expected))
    total+=1<<n
    row={'length':n,'words':1<<n,'minimum':smallest,'extremal_words':len(extremal),'passed':True}
    rows.append(row)
    log+=json.dumps(row)+'\n'


receipt={'status':'passed','lengths':[1,14],'word_count':total,'rows':rows,
         'finite_check_is_general_proof':False}
Path(__file__).with_name('independent-results.json').write_text(json.dumps(receipt,indent=2),encoding='utf-8')
print(log,end='')
print('ALL OK:',total,'words; minimum and complete extremal list checked.')
