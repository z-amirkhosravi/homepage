"""Verify the finite arithmetic certificate. Python 3 + SymPy; no network or PARI."""
from pathlib import Path
from itertools import product
from math import factorial, isqrt
import importlib.util, json, time
import sympy as S

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('polynomials',ROOT/'certificate-polynomials.py')
P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
data=json.loads((ROOT/'arithmetic-certificate.json').read_text())
K=data['kernel'];B=data['brandt']
mat=lambda x:S.Matrix(x).applyfunc(S.Rational)
serial=lambda M:[[str(x) for x in row] for row in M.tolist()]
result={}
def record(name,value=True):
    result[name]=value
    print(name, value,flush=True)
def qmul(a,b):
    t,x,y,z=a;T,X,Y,Z=b
    return S.Matrix([t*T-2*x*X-5*y*Y-10*z*Z,
                     t*X+x*T+5*(y*Z-z*Y),
                     t*Y+y*T+2*(z*X-x*Z),t*Z+z*T+x*Y-y*X])
def closure(gens):
    found={tuple(S.eye(4)):S.eye(4)};pending=[S.eye(4)]
    while pending:
        g=pending.pop()
        for h in gens:
            gh=g*h
            if tuple(gh) not in found:found[tuple(gh)]=gh;pending.append(gh)
    return list(found.values())
def vectors(A,bound):
    # If z^t A z <= bound, Cauchy--Schwarz gives
    # z_i^2 <= bound (A^-1)_ii. This is an exhaustive integer box.
    inv=A.inv();bounds=[isqrt(int(S.floor(bound*inv[i,i]))) for i in range(4)]
    coeff=[[int(x) for x in row] for row in A.tolist()]
    out=[]
    for z in product(*(range(-b,b+1) for b in bounds)):
        n=sum(z[i]*coeff[i][j]*z[j] for i in range(4) for j in range(4))
        if 0<n<=bound:out.append((S.Matrix(z),n))
    return out
def evaluate(poly,z):
    return sum(c*S.prod(x**a for x,a in zip(z,e)) for e,c in poly.items())
O=mat(K['order_basis_columns']);I=mat(K['ideal_basis_columns'])
alpha=mat(K['principal_generator']);Lalpha=S.Matrix.hstack(*(qmul(alpha,S.eye(4)[:,j]) for j in range(4)))
metric=S.diag(1,2,5,10);A=2*O.T*metric*O;AI=I.T*metric*I
C=(Lalpha*O).inv()*I
assert abs(C.det())==1 and all(x.q==1 for x in C)
assert (alpha.T*metric*alpha)[0]==2
assert AI==S.Matrix([[4,0,1,3],[0,8,2,5],[1,2,2,2],[3,5,2,6]])
assert A.det()==AI.det()==25
for M in [A,AI]:
    level=5*M.inv()
    assert all(x.q==1 for x in level) and all(level[i,i]%2==0 for i in range(4))
    assert any(x.q!=1 for x in M.inv())
for i,j in product(range(4),repeat=2):
    assert all(x.q==1 for x in O.inv()*qmul(O[:,i],O[:,j]))
    assert all(x.q==1 for x in I.inv()*qmul(I[:,i],O[:,j]))
assert any(x.q!=1 for x in I.inv()*S.Matrix([1,0,0,0]))
record('order_and_principal_ideal')

gens=[mat(g) for g in K['proper_group_generators']]
J=mat(K['order_conjugation_matrix'])
group=closure(gens);full=closure(gens+[J])
assert len(group)==36 and len(full)==72
assert all(g.T*A*g==A for g in full)
# Enumerate all possible columns of an integral isometry and impose pairings.
candidates=[[z for z,n in vectors(A,int(A[j,j])) if n==A[j,j]] for j in range(4)]
iso=[]
def extend(cols):
    j=len(cols)
    if j==4:
        iso.append(S.Matrix.hstack(*cols));return
    for v in candidates[j]:
        if all((c.T*A*v)[0]==A[i,j] for i,c in enumerate(cols)):extend(cols+[v])
extend([])
assert {tuple(g) for g in iso}=={tuple(g) for g in full}
record('exhaustive_isometry_orders',{'proper':36,'full':72})
es=[tuple(e) for e in K['monomial_exponents']]
H=mat(K['invariant_basis_columns']);es4=P.exponents(4)
lap=[]
for e in es:
    f={e:P.F(1)}
    q=P.add(*(P.scale(P.deriv(P.deriv(f,i),j),P.F(A.inv()[i,j])) for i,j in product(range(4),repeat=2)))
    lap.append(S.Matrix([q.get(a,0) for a in es4]))
D=S.Matrix.hstack(*lap)
actions=[P.transform_matrix(g,es) for g in gens]
equations=S.Matrix.vstack(D,*(a-S.eye(84) for a in actions))
assert equations.to_DM().rank()==79 and H.to_DM().rank()==5 and equations*H==S.zeros(equations.rows,5)
actJ=P.transform_matrix(J,es)
assert S.Matrix.vstack(equations,actJ-S.eye(84)).to_DM().rank()==80
assert actJ*H==H*mat(K['conjugation_on_invariants'])
# Quartic invariant dimension via the same equations.
e4=P.exponents(4);e2=P.exponents(2)
d4=S.Matrix.hstack(*(S.Matrix([f.get(a,0) for a in e2]) for e in e4 for f in
 [P.add(*(P.scale(P.deriv(P.deriv({e:P.F(1)},i),j),P.F(A.inv()[i,j])) for i,j in product(range(4),repeat=2)))]))
assert S.Matrix.vstack(d4,*(P.transform_matrix(g,e4)-S.eye(len(e4)) for g in gens)).to_DM().rank()==len(e4)-1
record('harmonic_invariant_dimensions',{'degree4_proper':1,'degree6_proper':5,'degree6_full':4})
shells={n:[] for n in range(1,6)}
for z,n in vectors(A,10):shells[int(n//2)].append(z)
moments=S.Matrix([[sum(S.prod(z[i]**e[i] for i in range(4)) for z in shells[n]) for e in es] for n in range(1,5)])
theta=moments*H
assert theta==mat(K['theta_coefficients_rows_n1_to16'][:4]) and theta.to_DM().rank()==3
record('shell_rows',serial(theta))
record('shell_sizes_1_to5',[len(shells[n]) for n in range(1,6)])

# Three-dimensional unit-invariant space, compressed matrix coefficients.
X=S.symbols('X Y Z');qvars=S.symbols('t u v w')
e3=[tuple(e) for e in B['ternary_exponents']]
WB=mat(B['W_basis_columns'])
conj=S.diag(1,-1,-1,-1)
def adjoint(q):
    return S.Matrix.hstack(*(qmul(qmul(conj*q,S.eye(4)[:,j]),q)[1:4,0] for j in [1,2,3]))
units=[O*z for z in shells[1]]
assert len(units)==6
Pi=sum((P.transform_matrix(adjoint(q),e3) for q in units),S.zeros(10))/6
assert Pi*WB==WB and WB.to_DM().rank()==3
e1=P.exponents(1,3)
lap3=S.Matrix.hstack(*(S.Matrix([f.get(a,0) for a in e1]) for e in e3 for f in
 [P.add(*(P.scale(P.deriv(P.deriv({e:P.F(1)},i),i),P.F(1,n)) for i,n in enumerate([2,5,10])))]))
assert S.Matrix.vstack(lap3,Pi-S.eye(10)).to_DM().rank()==7
record('unit_invariant_harmonic_cubic_dimension',3)
for col in range(3):
    f=P.poly(WB[:,col],e3)
    assert not P.add(*(P.scale(P.deriv(P.deriv(f,i),i),P.F(1,n)) for i,n in enumerate([2,5,10])))
rows=list(WB.T.rref()[1]);left=WB[rows,:].inv()*Pi[rows,:]
R=[]
for j in range(3):
    f=S.Poly(S.expand(P.expression(P.poly(WB[:,j],e3),adjoint(S.Matrix(qvars))*S.Matrix(X))),*X)
    R.append(S.Matrix([f.coeff_monomial(e) for e in e3]))
compressed=(left*S.Matrix.hstack(*R)).applyfunc(S.expand)
expected=S.Matrix(B['compressed_representation']).applyfunc(S.sympify)
assert compressed==expected
coeff=lambda f:S.Matrix([S.Poly(S.expand(f),*qvars).coeff_monomial(e) for e in es])
assert S.Matrix.hstack(*(coeff(f) for f in compressed)).to_DM().rank()==9
for n in range(1,6):
    total=sum((P.transform_matrix(adjoint(O*z),e3)*WB for z in shells[n]),S.zeros(10,3))
    assert left*total/6==mat(B['brandt_matrices'][str(n)])
for ab in B['commutant_T5_basis']:
    f=P.poly(coeff(S.trace(mat(ab)*compressed)),es)
    op=P.substitute(f,O);vec=S.Matrix([op.get(e,0) for e in es])
    assert equations*vec==S.zeros(equations.rows,1)
GW=mat(B['W_inner_product'])
fischer=S.diag(*(S.prod(S.Rational(factorial(k),a**k) for k,a in zip(e,[2,5,10])) for e in e3))
assert GW==WB.T*fischer*WB and all(GW[:i,:i].det()>0 for i in range(1,4))
for name in ['even','odd']:
    ab=mat(B['kernel_matrices'][name])
    target=mat(K['kernel'][name]['coefficients_in_quaternion_coordinates'])
    assert coeff(S.trace(ab*compressed))==S.Rational(B['kernel_polynomial_multipliers'][name])*target
    assert GW*ab==(1 if name=='even' else -1)*ab.T*GW
record('brandt_coefficients_and_kernel_polynomials')

# Remove a common square root from Euclidean numerator components.
def rational_pullback(nu,axis,change):
    pa=(nu[0]+nu[2]+int(axis in (1,3)))%2
    pb=(nu[1]+nu[2]+int(axis in (2,3)))%2
    f={e:P.F(c)*2**((e[1]+e[3]-pa)//2)*5**((e[2]+e[3]-pb)//2) for e,c in P.numerator(nu)[axis].items()}
    return P.substitute(f,change),2**pa*5**pb
mixed=[]
for nu in product(range(6),repeat=3):
    if sum(nu)!=5 or sum(n>0 for n in nu)<2:continue
    for axis in range(4):
        f,radical=rational_pullback(nu,axis,Lalpha*O)
        avg=P.scale(P.add(*(P.substitute(f,g) for g in group)),P.F(1,36))
        v=S.Matrix([avg.get(e,0) for e in es])
        if not mixed or S.Matrix.hstack(*(v0 for _,_,v0 in mixed),v).to_DM().rank()>len(mixed):mixed.append((nu,axis,v))
        if len(mixed)==5:break
    if len(mixed)==5:break
record('independent_mixed_averages',[{'nu':list(nu),'component':axis,'basis_coordinates':list(map(str,H.gauss_jordan_solve(v)[0]))} for nu,axis,v in mixed])
assert len(mixed)==5
polys=[];unaveraged=[]
for nu,axis,c in [((0,4,1),1,2),((1,0,4),3,3),((2,0,3),1,1)]:
    f,radical=rational_pullback(nu,axis,Lalpha*O)
    assert radical==5
    polys.append(P.scale(f,c));unaveraged.append(P.scale(P.numerator(nu)[axis],c))
avg=P.scale(P.add(*(P.substitute(P.add(*polys),g) for g in full)),P.F(1,72))
target=P.substitute(P.poly(mat(K['kernel']['even']['coefficients_in_quaternion_coordinates']),es),O)
assert avg==P.scale(target,-12000)
counter=S.Rational(evaluate(P.add(*unaveraged),[1,1,0,1]),3**7)
assert counter==-S.Rational(1280,243)
record('averaged_relation_and_regular_counterexample',str(counter))
theta3=[]
expected=[-60*S.sqrt(2),-12,24*S.sqrt(10),12*S.sqrt(5)]
for axis in range(4):
    f,radical=rational_pullback((1,2,0),axis,Lalpha*O)
    values=[S.sqrt(radical)*sum(evaluate(f,z) for z in shells[n]) for n in range(1,4)]
    assert values==[expected[axis]*c for c in [1,2,-4]]
    theta3.append(list(map(str,values)))
record('order3_shell_components',theta3)
result['passed']=True
(ROOT/'certificate-checks.json').write_text(json.dumps(result,indent=2)+'\n')
