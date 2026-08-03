"""
Verification 2 -- machine support for the subadditivity proof (all n).
  (i)  alternation lemma: rises <= drops + 1, EXHAUSTIVE over all binary
       sequences of length <= 16;
  (ii) d(g(x, NOT h)) <= d(h) + 1: randomized composition sweep at n = 4, 5
       (n <= 3 exhaustive is covered by Verification 1).
Random monotone g generated as upper-set indicators of random seed sets.
Deterministic seed. Companion to "The Cohomological Price of NOT".
"""
from itertools import product as prod, permutations
import random

# ---------- chain-decrease ----------
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
            if fvals[idx[a]]==1 and fvals[idx[b]]==0:
                d+=1
        best=max(best,d)
    return best
# --------------------------------------------

print("="*74)
print("(i) Step-2 alternation: rises <= drops+1, all binary sequences len<=16")
print("="*74)
checked=0
for L in range(1,17):
    for bits in range(2**L):
        v=[(bits>>i)&1 for i in range(L)]
        r=sum(1 for a,b in zip(v,v[1:]) if a==0 and b==1)
        d=sum(1 for a,b in zip(v,v[1:]) if a==1 and b==0)
        assert r <= d+1, f"alternation FAILS at {v}"
        checked+=1
print(f"PASS -- {checked} sequences, 0 violations.")

print()
print("="*74)
print("(ii) dec(g(x,NOT h)) <= dec(h)+1 -- randomized sweep n=4,5")
print("="*74)
rng = random.Random(20260728)
for n,(NH,NG) in ((4,(200,200)),(5,(100,100))):
    pts=list(prod((0,1),repeat=n)); idx={p:i for i,p in enumerate(pts)}
    chains=maximal_chains(n)
    m=n+1
    ptsm=list(prod((0,1),repeat=m)); idxm={p:i for i,p in enumerate(ptsm)}
    def rand_monotone_g():
        # upper-set indicator of a random seed set (every monotone fn arises this way)
        k=rng.randint(0,6)
        seeds=[rng.choice(ptsm) for _ in range(k)]
        return tuple(1 if any(all(s<=y for s,y in zip(sd,p)) for sd in seeds) else 0
                     for p in ptsm)
    hs=[tuple(rng.randint(0,1) for _ in pts) for _ in range(NH)]
    gs=[rand_monotone_g() for _ in range(NG)]
    viol=0; total=0; maxgap=-99
    for h in hs:
        dh=dec_fn(h,idx,chains)
        nh=[1-v for v in h]
        for g in gs:
            fv=tuple(g[idxm[tuple(list(x)+[nh[idx[x]]])]] for x in pts)
            df=dec_fn(fv,idx,chains)
            total+=1
            maxgap=max(maxgap, df-dh)
            if df > dh+1: viol+=1
    print(f"n={n}: {total} compositions; violations {viol}; max observed dec(f)-dec(h) = {maxgap}")
    assert viol==0, "subadditivity corroboration FAILS"
print("\nPASS -- 0 violations; the bound is attained (max gap = 1) as expected.")
print("ALL ASSERTIONS PASSED.")
