# Numerical check of Malfatti radius formula r_A = r/(2(s-a)) (s - r - (IB+IC-IA)),
# centres on bisectors O_A = A + (r_A/r)(I-A); tangency to sides and pairwise.
import math, random
def dist(P,Q): return math.hypot(P[0]-Q[0],P[1]-Q[1])
def linedist(O,P,Q):
    return abs((Q[0]-P[0])*(O[1]-P[1])-(Q[1]-P[1])*(O[0]-P[0]))/dist(P,Q)
def malf(A,B,C,wrong=False):
    a,b,c=dist(B,C),dist(C,A),dist(A,B); s=(a+b+c)/2
    I=tuple((a*A[i]+b*B[i]+c*C[i])/(2*s) for i in range(2))
    r=math.sqrt((s-a)*(s-b)*(s-c)/s)
    def rad(P,Q,R,p,q,w):  # vertex P, opposite side length p
        x=s-p; return r/(2*x)*(s-r-(dist(I,Q)+dist(I,R)-dist(I,P)) + (0.01 if wrong else 0))
    rho=[rad(A,B,C,a,b,c),rad(B,C,A,b,c,a),rad(C,A,B,c,a,b)]
    V=[A,B,C]; O=[tuple(V[k][i]+rho[k]/r*(I[i]-V[k][i]) for i in range(2)) for k in range(3)]
    err=0
    for k in range(3):
        for j in range(3):
            if j!=k: err=max(err,abs(linedist(O[k],V[k],V[j])-rho[k]))
        err=max(err,abs(dist(O[k],O[(k+1)%3])-rho[k]-rho[(k+1)%3]))
    return err,rho,r
random.seed(1); worst=0; worstbad=1e9
for _ in range(2000):
    A,B,C=[(random.uniform(-5,5),random.uniform(-5,5)) for _ in range(3)]
    area=abs((B[0]-A[0])*(C[1]-A[1])-(B[1]-A[1])*(C[0]-A[0]))/2
    if area<1e-2: continue
    worst=max(worst,malf(A,B,C)[0]); worstbad=min(worstbad,malf(A,B,C,True)[0])
print("max tangency error (formula):",worst)
print("min tangency error (negative control, perturbed):",worstbad)
assert worst<1e-8 and worstbad>1e-5
# Lob-Richmond: equilateral side 1
A,B,C=(0,0),(1,0),(0.5,math.sqrt(3)/2)
_,rho,r=malf(A,B,C)
m=math.pi*sum(t*t for t in rho); g=math.pi*(r*r+2*(r/3)**2)
print("equilateral: Malfatti area %.6f < incircle+2 corner circles %.6f"%(m,g)); assert m<g
