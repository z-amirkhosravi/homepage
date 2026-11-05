"""Exact sparse polynomial operations used by the arithmetic certificate."""
from fractions import Fraction as F
from itertools import product
import sympy as S

def add(*polys):
    out = {}
    for poly in polys:
        for e, c in poly.items():
            out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}

def scale(poly, c):
    return {e: v*c for e, v in poly.items() if v*c}

def mul(a, b):
    out = {}
    for e, c in a.items():
        for f, d in b.items():
            g = tuple(x+y for x, y in zip(e, f))
            out[g] = out.get(g, 0) + c*d
    return {e: c for e, c in out.items() if c}

def deriv(poly, axis):
    out = {}
    for e, c in poly.items():
        if e[axis]:
            f = list(e)
            f[axis] -= 1
            out[tuple(f)] = c*e[axis]
    return out

V = [{tuple(int(j == a) for j in range(4)): 1} for a in range(4)]
N = add(*(mul(v, v) for v in V))

def numerator(nu):
    h = [V[0], *(scale(v, -1) for v in V[1:])]
    axes = [a+1 for a, n in enumerate(nu) for _ in range(n)]
    for r, axis in enumerate(axes):
        h = [add(mul(N, deriv(poly, axis)),
                 scale(mul(V[axis], poly), -2*(r+2))) for poly in h]
    for poly in h:
        assert not add(*(deriv(deriv(poly, a), a) for a in range(4)))
    return h

def exponents(degree,n=4):
    return [e for e in product(range(degree+1),repeat=n) if sum(e)==degree]

def power(p,n):
    out={(0,)*len(next(iter(p))):F(1)}
    for _ in range(n):out=mul(out,p)
    return out

def substitute(p,M):
    n=M.cols
    linear=[{tuple(int(k==j) for k in range(n)):F(M[i,j]) for j in range(n) if M[i,j]} for i in range(M.rows)]
    degree=max(map(sum,p)) if p else 0
    powers=[[power(l,j) for j in range(degree+1)] for l in linear]
    out={}
    for e,c in p.items():
        term={(0,)*n:c}
        for i,k in enumerate(e):term=mul(term,powers[i][k])
        out=add(out,term)
    return out

def transform_matrix(M,es):
    return S.Matrix.hstack(*(S.Matrix([p.get(f,0) for f in es]) for e in es for p in [substitute({e:F(1)},M)]))

def poly(v,es):
    return {e:F(c) for e,c in zip(es,v) if c}

def expression(p,variables):
    return S.Add(*(S.Rational(c)*S.prod(x**k for x,k in zip(variables,e)) for e,c in p.items()))
