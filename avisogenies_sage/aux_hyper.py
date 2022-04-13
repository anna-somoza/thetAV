from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
from sage.categories.homset import hom 

def remove_h(phi):
    C = phi.codomain()
    f, h = C.hyperelliptic_polynomials()
    f1 = f + h**2/4
    C1 = HyperellipticCurve(f1)
    x0,x1,x2 = C.defining_polynomial().parent().gens()
    phi1 = hom(C, C1, [x0/x2, x1/x2 + h(x0/x2)/2, 1])
    phi1.normalize_coordinates()
    return phi1*phi

def odd_degree_model(phi):
    C = phi.codomain()
    f, h = C.hyperelliptic_polynomials()
    if h:
        raise TypeError(f'Expected a hyperelliptic curve with h={h}=0')
    g = C.genus()
    if f.degree() != 2*g + 2:
        raise TypeError(f'Expected a hyperelliptic curve with even degree')
    rts = f.roots(multiplicities=False)
    if not rts:
        raise ValueError('No odd degree model exists over field of definition')
    a = rts[0]
    x = f.parent().gen()
    f1 = f((a*x + 1)/x).numerator()
    C1 = HyperellipticCurve(f1)
    x0,x1,x2 = C.defining_polynomial().parent().gens()
    phi1 = hom(C,C1, [1/(x0/x2 - a), (x1/x2)/(x0/x2 - a)**(g+1), 1])
    phi1.normalize_coordinates()
    return phi1*phi

def rosenhain_model(phi):
    C = phi.codomain()
    f, h = C.hyperelliptic_polynomials()
    if h:
        raise TypeError(f'Expected a hyperelliptic curve with h={h}=0')
    g = C.genus()
    if f.degree() != 2*g + 1:
        raise TypeError(f'Expected a hyperelliptic curve with odd degree')
    rts = f.roots()
    if sum(m for el,m in rts) != 2*g + 1:
        raise ValueError('No Rosenhain model exists over field of definition')
    rts.sort()
    a0 = rts[0][0]
    a1 = rts[1][0]
    x = f.parent().gen()
    f1 = f((a1 - a0)*x + a0)
    C1 = HyperellipticCurve(f1)
    x0,x1,x2 = C.defining_polynomial().parent().gens()
    phi1 = hom(C,C1, [(x0 - a0*x2)/(a1 - a0), x1, x2])
    return phi1*phi
