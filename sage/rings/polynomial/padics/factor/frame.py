from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.padics.factor.frameelt import FrameElt, FrameEltTerm
from sage.rings.polynomial.padics.factor.segment import Segment
from sage.rings.infinity import infinity
from sage.misc.functional import denominator

class Frame:
    """Everything for one iteration of local field polynomial factorization"""
    def __init__(self,Phi,pre=None,iteration_count=0):
        self.prev = pre
        self.Phi = Phi
        self.O = Phi.base_ring()
        self.Ox = Phi.parent()
        self.x = self.Ox.gen()
        self.R = self.O.residue_class_field()
        self.Rz = PolynomialRing(self.R,names='z')
        self.phi = None
        self.iteration = iteration_count + 1
        if self.is_first(): # that is self.prev == None
            self.E = 1
            self.F = 1
            self.depth = 0
        else:
            self.E = self.prev_frame().E * self.prev.segment.Eplus
            self.F = self.prev_frame().F * self.prev.Fplus
            self.depth = self.prev_frame().depth + 1

    def first(self):
        """
        Computes all of the frame data based on being the root of the tree of frames
        """
        self.phi = self.x
        self._expansion_of_Phi()
        self.polygon = self._newton_polygon([e.valuation() for e in self._phiexpelt]) # list of segments

    def is_first(self):
        return self.prev == None

    def seed(self,phi,length=infinity):
        """
        Computes all of the frame data with the new phi
        """
        self.phi = phi
        self._expansion_of_Phi(length=length)
        # If phi divides Phi, we may be in a leaf that resembles its parent
        # and need to break recursion
        if self.is_first() == False and self.phi == self.prev_frame().phi and self.phi_divides_Phi():
            return
        else:
            self.polygon = self._newton_polygon([e.valuation() for e in self._phiexpelt]) # list of segments

    def find_psi(self,val):
        psielt = FrameElt(self)
        if self.prev == None:
            psielt.rep = [FrameEltTerm(psielt,self.O(1),val)]
        else:
            vphi = self.prev.segment.slope
            d = self.prev_frame().E
            vprime = val*d
            e = vphi * d
            psimod = denominator(e)
            s = 0
            if not psimod == 1:
                s = vprime / e
                if denominator(s) == 1:
                    s = s % psimod
                else:
                    s = int(s % psimod)
            val = val - s * vphi
            psielt.rep = [FrameEltTerm(psielt,self.prev_frame().find_psi(val),s)]
        return psielt

    def _expansion_of_Phi(self,length=infinity):
        self._phiexppoly = []
        if self.phi.degree() > self.Phi.degree():
            self._phiexppoly = [self.Phi]
        q, r = self.Phi.quo_rem(self.phi)
        self._phiexppoly.append(r)
        while q != 0 and length > len(self._phiexppoly):
            q, r = q.quo_rem(self.phi)
            self._phiexppoly.append(r)
        self._phiexpelt = [FrameElt(self,a) for a in self._phiexppoly]

    def _newton_polygon(self,a,xoffset=0):
        if len(a) == 0:
            raise ValueError, "Cannot compute Newton polygon from empty list"

        # Handle the case where the first segment has infinite slope
        # (This will occur iff phi divides Phi)
        if self.phi_divides_Phi() and xoffset == 0:
            for i in range(1,len(a)):
                if a[i] < self.O.precision_cap():
                    verts = [(0,infinity),(i,a[i])]
                    slope = infinity
                    length = i
                    if i == len(a)-1:
                        return [Segment(self,slope,verts,length)]
                    else:
                        return [Segment(self,slope,verts,length)]+self._newton_polygon(a[verts[len(verts)-1][0]-xoffset:],verts[len(verts)-1][0])

        slope = (a[0]-a[len(a)-1]) / (len(a)-1)
        verts = [(xoffset,a[0])]
        length = 0
        for i in range(1,len(a)):
            y = a[0] - i*slope
            if a[i] == y:
                verts.append((xoffset+i,y))
                length = i
            elif a[i] < y:
                verts = [(xoffset,a[0]),(xoffset+i,a[i])]
                slope = (a[0]-a[i]) / i
                length = i
            elif y < 0:
                if len(a[verts[len(verts)-1][0]-xoffset:]) == 0:
                    return [Segment(self,slope,verts,length)]
                else:
                    return [Segment(self,slope,verts,length)]+self._newton_polygon(a[verts[len(verts)-1][0]-xoffset:],verts[len(verts)-1][0])
        return [Segment(self,slope,verts,length)]

    # Data Access Methods

    def prev_frame(self):
        if self.prev == None:
            return None
        else:
            return self.prev.segment.frame

    def elt_phi_expansion(self):
        return self._phiexpelt

    def phi_divides_Phi(self):
        """
        Returns whether or not phi divides Phi

        Checks to see if the constant term of the phi-expansion of Phi is 0
        """
        return self._phiexppoly[0] == 0

    def __repr__(self):
        if self.phi:
            return 'Frame with phi '+repr(self.phi)
        else:
            return 'Unseeded Frame regarding '+repr(self.Phi)
