"""
Verification 3 -- the three-zone witness, exhaustively (n <= 4) + sampled (n = 5).
For every nonconstant f with d(f) = k >= 1:
    h := 1 on {omega >= k},  NOT f on {1 <= omega <= k-1},  0 on {omega = 0}
must satisfy: covering (0 on V-, 1 on V+)  AND  monotone-g existence  AND
d(h) = k-1 exactly.  Deterministic seed.
Companion to "The Cohomological Price of NOT". ASCII-only, stdlib-only.
"""
from itertools import product as prod, permutations
import random

def maximal_chains(n):
    base=tuple([0]*n)
    chains=[]
    for perm in permutations(range(n)):
        chain=[base]; cur=list(base)
        for c in perm:
            cur=list(cur); cur[c]=1; chain.append(tuple(cur))
        chains.append(chain)
    return chains
def dec_fn(fvals, idx, chains):
    best=0
    for ch in chains:
        d=0
        for a,b in zip(ch, ch[1:]):
            if fvals[idx[a]]==1 and fvals[idx[b]]==0: d+=1
        best=max(best,d)
    return best
def setup(n):
    pts=list(prod((0,1),repeat=n)); idx={p:i for i,p in enumerate(pts)}
    chains=maximal_chains(n)
    le=[[all(x<=y for x,y in zip(a,b)) for b in pts] for a in pts]
    return pts,idx,chains,le
def omega(f, idx, chains, N):
    om=[0]*N
    for ch in chains:
        d=0
        for a,b in zip(ch, ch[1:]):
            if f[idx[a]]==1 and f[idx[b]]==0: d+=1
            j=idx[b]
            om[j]=max(om[j],d)
    return om

def check_one(f, pts, idx, chains, le, N):
    k=dec_fn(f,idx,chains)
    if k==0: return None
    om=omega(f,idx,chains,N)
    h=tuple(1 if om[i]>=k else (1-f[i] if om[i]>=1 else 0) for i in range(N))
    # covering + monotone-g existence: for all i<=j: h[i]>=h[j] and f[i]>f[j] is a violation
    for i in range(N):
        for j in range(N):
            if le[i][j] and h[i]>=h[j] and f[i]>f[j]:
                return ('g-extension FAIL', f, k)
    dh=dec_fn(h,idx,chains)
    if dh!=k-1:
        return ('dec FAIL', f, k, dh)
    return 'OK'

print("="*74)
print("h_gen: exhaustive n=2,3,4")
print("="*74)
for n in (2,3,4):
    pts,idx,chains,le=setup(n); N=len(pts)
    cnt=0; bad=[]
    per_k={}
    for f in prod((0,1),repeat=N):
        if len(set(f))==1: continue
        r=check_one(f,pts,idx,chains,le,N)
        if r is None: continue
        cnt+=1
        k=dec_fn(f,idx,chains)
        per_k[k]=per_k.get(k,0)+1
        if r!='OK': bad.append(r)
    print(f"n={n}: {cnt} nonmonotone f checked (by k: {dict(sorted(per_k.items()))}); failures: {len(bad)}")
    for b in bad[:5]: print('   ',b)
    assert not bad, "h_gen FAILS"
print("PASS -- covering + monotone-g + dec(h_gen)=k-1 exhaustively, n<=4.")

print()
print("="*74)
print("h_gen: random sample n=5 (2000 f, all k)")
print("="*74)
rng=random.Random(20260728)
n=5; pts,idx,chains,le=setup(n); N=len(pts)
per_k={}; bad=[]
for _ in range(2000):
    f=tuple(rng.randint(0,1) for _ in range(N))
    if len(set(f))==1: continue
    r=check_one(f,pts,idx,chains,le,N)
    if r is None: continue
    k=dec_fn(f,idx,chains)
    per_k[k]=per_k.get(k,0)+1
    if r!='OK': bad.append(r)
print(f"n=5: checked by k: {dict(sorted(per_k.items()))}; failures: {len(bad)}")
for b in bad[:5]: print('   ',b)
assert not bad, "h_gen FAILS at n=5"
print("PASS.")
print("\nALL ASSERTIONS PASSED.")
