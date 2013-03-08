from sage.rings.polynomial.padics.factor.associatedfactor import AssociatedFactor
from sage.rings.arith import gcd
from sage.rings.infinity import infinity

class Segment:

    def __init__(self,frame,slope,vert,length):
        """
        Initialises self.

        EXAMPLES::

        """
        self.frame = frame
        self.vertex = vert
        self.slope = slope
        self.length = length
        self.Eplus = self.e() / gcd(self.e(),int(self.frame.E))
        if slope != infinity:
            self.psi = self.frame.find_psi(self.slope*self.Eplus)
        self._associate_polynomial = self.associate_polynomial(cached=False)
        self.factors = [AssociatedFactor(self,afact[0],afact[1]) 
                        for afact in list(self._associate_polynomial.factor())]

    def h(self):
        """
        Return the numerator of the slope of this segment.

        EXAMPLES::

        """
        if isinstance(self.slope,PlusInfinity):
            return self.slope
        if isinstance(self.slope,int):
            return self.slope.numerator
        else:
            return self.slope.numerator()
    def e(self):
        """
        Return the denominator of the slope of this segment.

        EXAMPLES::

        """
        if self.slope == infinity:
            return 1
        if isinstance(self.slope,int):
            return self.slope.denominator
        else:
            return self.slope.denominator()

    def vphi(self):
        """
        Return the slope of this segment.

        EXAMPLES::

        """
        return self.slope

    def associate_polynomial(self,cached=True):
        """
        Return the associated polynomial of this segment.

        INPUT:

        - ``cached`` - Boolean; default TRUE. If TRUE, returns the cached associated
          polynomial. If FALSE, complutes the associated polynomial anew.

        OUTPUT:

        - 

        EXAMPLES:
        """
        if cached:
            return self._associate_polynomial()

        if self.slope == infinity:
            if self.frame.prev == None:
                Az = self.frame.Rz.gen() ** self.length
            else:
                Az = self.frame.prev.FFz.gen() ** self.length
            return Az

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
        """
        Representation of self.
        
        EXAMPLES::

        """
        return 'Segment of length '+repr(self.length)+' and slope '+repr(self.slope)
