from sage.rings.polynomial.padics.factor.associatedfactor import AssociatedFactor
from sage.rings.arith import gcd

class Segment:

    def __init__(self,frame,slope,vert,length):
        self.frame = frame
        self.vertex = vert
        self.slope = slope
        self.length = length
        self.Eplus = self.e() / gcd(self.e(),int(self.frame.E))
        if self.frame.E * self.frame.F * self.Eplus < self.frame.Phi.degree():
            self.psi = self.frame.find_psi(self.slope*self.Eplus)
            self._associate_polynomial = self.associate_polynomial(cached=False)
            self.factors = [AssociatedFactor(self,afact[0],afact[1]) for afact in list(self._associate_polynomial.factor())]
        else:
            # Polynomial is irreducible
            return

    def h(self):
        if isinstance(self.slope,int):
            return self.slope.numerator
        else:
            return self.slope.numerator()
    def e(self):
        if isinstance(self.slope,int):
            return self.slope.denominator
        else:
            return self.slope.denominator()

    def vphi(self):
        return self.slope

    def associate_polynomial(self,cached=True):
        if cached:
            return self._associate_polynomial()
        else:
            a = self.frame.elt_phi_expansion()
            vertx = [v[0] for v in self.vertex]
            chiex = [int((v-vertx[0]) // self.Eplus) for v in vertx]
            chi = [a[vertx[i]] * self.psi**chiex[i] for i in range(len(vertx))]
            psitilde = self.frame.find_psi(chi[0].valuation())
            Ahat = [(c/psitilde).reduce() for c in chi]
            if self.frame.prev == None:
                Az = sum([(Ahat[i].residue()) * self.frame.Rz.gen() ** chiex[i] for i in range(len(Ahat))])
            else:
                Az = sum([(Ahat[i].residue()) * self.frame.prev.FFz.gen() ** chiex[i] for i in range(len(Ahat))])
            return Az

    def __repr__(self):
        return 'Segment of length '+repr(self.length)+' and slope '+repr(self.slope)