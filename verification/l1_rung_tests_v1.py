"""
Verification 1 -- rung structure of the decrease ladder (exhaustive, n <= 3).
  (b) gate typing:   on the Klein four-group V4 = <sigma, P> acting on the
                     dual-rail lattice, the negation cost nu(gamma) equals the
                     chi_sigma coordinate pointwise; the face-flip character
                     (chi_sigma + chi_P) mis-prices in BOTH directions
                     (witnesses: P and sigma P).
  (a) peel-one:      every f with d(f) = k >= 1 factors as f = g(x, NOT h(x))
                     with g monotone and d(h) = k-1 EXACTLY (no skipping).
  (c) subadditivity: d(g(x, NOT h)) <= d(h) + 1 for all monotone g, all h.
Companion to "The Cohomological Price of NOT". ASCII-only, stdlib-only.
"""
from itertools import product as prod, permutations

# ---------- characters via extension classes ----------
enc = {0:(0,0),1:(1,0),2:(0,1),3:(1,1)}; dec_map={v:k for k,v in enc.items()}
def sigma_s(i):
    a,b=enc[i]; return dec_map[(1-a,1-b)]
def P(i):
    a,b=enc[i]; return dec_map[(b,a)]
def comp(f,g): return lambda i: f(g(i))
sP = comp(sigma_s,P)
ident = lambda i: i
elts = {'id':ident,'sigma_s':sigma_s,'P':P,'sP':sP}
def ext_class(states):
    s0,s1 = states
    res={}
    for nm,f in elts.items():
        if nm=='id': continue
        img0=f(s0); img1=f(s1)
        assert set([img0,img1])==set([s0,s1])
        res[nm]= 0 if img0==s0 else 1
    return res
W2 = ext_class([1,2])   # face-flip = chi_sigma + chi_P
W1 = ext_class([0,3])   # chi_sigma (endpoint axis)
def char_at(cls, g): return 0 if g=='id' else cls[g]

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
# ---------------------------------------------------

print("="*74)
print("gate typing -- gate-level typing on V4: nu(gamma) = chi_sigma(gamma)")
print("="*74)
le_k = {(0,0),(1,1),(2,2),(3,3),(0,1),(0,2),(1,3),(2,3),(0,3)}   # knowledge order
def is_k_monotone(f): return all((f(a),f(b)) in le_k for (a,b) in le_k)
print(f"{'gamma':>8} | {'k-monotone':>10} | {'nu':>3} | {'chi_sigma':>9} | {'face-flip':>5}")
for nm,f in elts.items():
    mono = is_k_monotone(f)
    nu = 0 if mono else 1     # monotone => in G (id, P are G-terms); non-monotone V4 elt
                              # = sigma_s or sigma_s.P => exactly one sigma_s suffices & is needed
    cs = char_at(W1,nm); cy = char_at(W2,nm)
    print(f"{nm:>8} | {str(mono):>10} | {nu:>3} | {cs:>9} | {cy:>5}")
    assert nu == cs, f"gate typing FAILS at {nm}: nu={nu} chi_sigma={cs}"
# face-flip fails as indicator exactly at P (and at sP in the other direction):
assert char_at(W2,'P')==1 and 0==(0 if is_k_monotone(P) else 1), "witness drifted"
assert char_at(W2,'sP')==0 and not is_k_monotone(sP), "sP: face-flip=0 but nu=1 (2nd separator)"
print("\n[gate typing VERDICT] PASS -- nu = chi_sigma pointwise on V4.")
print("  face-flip mis-indicates at BOTH P (face-flip=1,nu=0) and sP (face-flip=0,nu=1) -- the dec")
print("  axis is the chi_sigma coordinate, not the face-flip .")

print()
print("="*74)
print("peel-one -- peel-one exact decrement (recovered R-model), exhaustive n=2,3")
print("="*74)

def monotone_ok_partial(fv, hv, pts, idx, le_pairs):
    """exists monotone g with f(x)=g(x, NOT h(x)) ?
    Domain points (x, u=NOT h(x)) with product order; partial assignment f0(x,u)=f(x)
    extends to a total monotone g iff no pair violates:
      x<=x' and u(x)<=u(x')  [i.e. h(x)>=h(x')]  but f(x)>f(x')."""
    for (a,b) in le_pairs:
        if hv[idx[a]] >= hv[idx[b]] and fv[idx[a]] > fv[idx[b]]:
            return False
    return True

for n in (2,3):
    pts = list(prod((0,1), repeat=n)); idx={p:i for i,p in enumerate(pts)}
    chains = maximal_chains(n)
    le_pairs = [(a,b) for a in pts for b in pts if all(x<=y for x,y in zip(a,b))]
    allf = [f for f in prod((0,1), repeat=2**n)]
    decs = {f: dec_fn(f, idx, chains) for f in allf}
    byk={}
    for f,d in decs.items():
        if len(set(f))>1: byk.setdefault(d,[]).append(f)
    fails_exist=0; fails_lower=0; tested=0
    for k in sorted(byk):
        if k==0: continue
        for f in byk[k]:
            tested+=1
            # existence: some h with dec(h)=k-1 and monotone g
            ok = any(monotone_ok_partial(f,h,pts,idx,le_pairs)
                     for h in allf if decs[h]==k-1)
            if not ok: fails_exist+=1
            # lower bound: NO h with dec(h)<=k-2 works
            if k>=2:
                bad = any(monotone_ok_partial(f,h,pts,idx,le_pairs)
                          for h in allf if decs[h]<=k-2)
                if bad: fails_lower+=1
    kdist = {k:len(v) for k,v in sorted(byk.items())}
    print(f"n={n}: dec-distribution {kdist}; peel tested {tested} non-monotone f; "
          f"existence-fails {fails_exist}; lower-bound-fails {fails_lower}")
    assert fails_exist==0 and fails_lower==0, "peel-one FAILS"
print("\n[peel-one VERDICT] PASS -- every f with dec=k>=1 peels as f=g(x,NOT h), g monotone,")
print("  dec(h)=k-1 EXACTLY (never k-2 or less). One chi_sigma-twist per rung, no skipping:")
print("  the dec-ladder IS a k-step iterated-extension tower at n<=3.")

print()
print("="*74)
print("subadditivity -- subadditivity dec(g(x, NOT h)) <= dec(h)+1, exhaustive n=2,3")
print("="*74)

for n in (2,3):
    pts = list(prod((0,1), repeat=n)); idx={p:i for i,p in enumerate(pts)}
    chains = maximal_chains(n)
    # all monotone g on n+1 vars (including constants; product order), via filter
    m=n+1
    ptsm=list(prod((0,1),repeat=m)); idxm={p:i for i,p in enumerate(ptsm)}
    lem=[(a,b) for a in ptsm for b in ptsm if all(x<=y for x,y in zip(a,b))]
    monos=[g for g in prod((0,1),repeat=2**m)
           if all(g[idxm[a]]<=g[idxm[b]] for (a,b) in lem)]
    allf=[f for f in prod((0,1),repeat=2**n)]
    dech={h: dec_fn(h, idx, chains) for h in allf}
    viol=0; total=0
    for h in allf:
        nh=[1-v for v in h]
        for g in monos:
            fv=tuple(g[idxm[tuple(list(x)+[nh[idx[x]]])]] for x in pts)
            total+=1
            if dec_fn(fv, idx, chains) > dech[h]+1:
                viol+=1
    print(f"n={n}: {len(monos)} monotone g x {len(allf)} h = {total} compositions; "
          f"violations: {viol}")
    assert viol==0, "subadditivity FAILS"
print("\n[subadditivity VERDICT] PASS -- one adjoined twist raises dec by at most 1.")
print("  (With peel-one existence this pins dec(f) = minimal tower length exactly.)")
print("\nALL ASSERTIONS PASSED.")
