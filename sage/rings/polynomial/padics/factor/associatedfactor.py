from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.finite_rings.constructor import GF
from sage.matrix.constructor import Matrix
from sage.rings.polynomial.padics.factor.frameelt import FrameElt
from sage.rings.infinity import infinity

class AssociatedFactor:

    def __init__(self,segment,rho,rhoexp):
        self.segment = segment
        self.rho = rho
        self.rhoexp = rhoexp
        self.Fplus = self.rho.degree()

        if self.segment.frame.is_first():
            # In the first frame, so FFbase is the residue class field of O
            self.FFbase = self.segment.frame.R
        else:
            # Not the first frame
            self.FFbase = self.segment.frame.prev.FF

        if self.Fplus == 1:
            self.FF = self.FFbase
            self.FFz = PolynomialRing(self.FF,'z'+str(self.segment.frame.depth))
            # rho is linear delta is the root of rho
            self.delta = self.rho.roots()[0][0]
        else:
            self.FF = GF(self.FFbase.order()**self.Fplus,'a'+str(self.segment.frame.depth))
            self.FFz = PolynomialRing(self.FF,'z'+str(self.segment.frame.depth))
            self.FFbase_gamma = (self.FFz(self.FFbase.modulus())).roots()[0][0]
            FFrho = self.FFz([self.FFbase_elt_to_FF(a) for a in list(rho)])
            self.gamma = FFrho.roots()[0][0]
            basis = [(self.gamma**j*self.FFbase_gamma**i).polynomial() for j in range(0,self.Fplus) for i in range(0,self.FFbase.degree())]
            self.basis_trans_mat = Matrix([self.FF(b)._vector_() for b in basis])

    def FF_elt_to_FFbase_vector(self,a):
        if self.segment.frame.is_first() and self.Fplus == 1:
            return a
        elif self.Fplus == 1:
            return self.segment.frame.prev.FF_elt_to_FFbase_vector(a)
        else:
            basedeg = self.FFbase.degree()
            avec = self.FF(a)._vector_()
            svector = self.basis_trans_mat.solve_left(Matrix(self.FF.prime_subfield(),avec))
            s_list = svector.list()
            s_split = [ s_list[i*basedeg:(i+1)*basedeg] for i in range(0,self.Fplus)]
            s = [sum([ss[i]*self.FFbase.gen()**i for i in range(0,len(ss))]) for ss in s_split]
            return s

    def FFbase_elt_to_FF(self,b):
        if self.segment.frame.is_first():
            return b
        elif self.Fplus == 1:
            return self.segment.frame.prev.FFbase_elt_to_FF(b)
        elif self.segment.frame.F == 1:
            return b * self.FFbase_gamma
        else:
            bvec = b._vector_()
            return sum([ bvec[i]*self.FFbase_gamma**i for i in range(len(bvec))])

    def __repr__(self):
        return "AssociatedFactor of rho "+repr(self.rho)

    def lift(self,delta):
        # FrameElt representation of a lift of delta
        if self.segment.frame.F == 1:
            return FrameElt(self.segment.frame,self.segment.frame.Ox(delta))
        elif self.segment.frame.prev.Fplus == 1:
            return FrameElt(self.segment.frame,self.segment.frame.prev.lift(delta),this_exp=0)
        else:
            dvec = self.segment.frame.prev.FF_elt_to_FFbase_vector(delta)
            return sum([self.segment.frame.prev.gamma_frameelt**i*FrameElt(self.segment.frame,self.segment.frame.prev.lift(dvec[i]),this_exp=0) for i in range(len(dvec)) if dvec[i] != 0])

    def next_frame(self,length=infinity):
        from frame import Frame
        if self.segment.slope == infinity:
            next = Frame(self.segment.frame.Phi,self,self.segment.frame.iteration)
            self.next = next
            next.seed(self.segment.frame.phi,length=length)
            return next            
        if self.Fplus == 1 and self.segment.Eplus == 1:
            next = Frame(self.segment.frame.Phi,self.segment.frame.prev,self.segment.frame.iteration)
        else:
            next = Frame(self.segment.frame.Phi,self,self.segment.frame.iteration)
        self.next = next
        self.gamma_frameelt = FrameElt(next,self.segment.psi**-1,self.segment.Eplus)
        if self.Fplus == 1 and self.segment.frame.F == 1:
            next_phi = self.segment.frame.phi**self.segment.Eplus-(self.segment.psi.polynomial()*self.segment.frame.Ox(self.delta))
            self.reduce_elt = FrameElt(next,self.segment.psi*self.lift(self.delta),0)
            next.seed(next_phi,length=length)
        elif self.Fplus == 1 and self.segment.Eplus == 1:
            delta_elt = self.lift(self.delta)
            next_phi_tail = self.segment.psi*delta_elt.reduce()
            next_phi = self.segment.frame.phi-next_phi_tail.polynomial()
            self.reduce_elt = FrameElt(next,next_phi_tail,0)
            next.seed(next_phi,length=length)
        else:
            lifted_rho_coeffs = [self.lift(r) for r in list(self.rho)]
            lifted_rho_coeffs_with_psi = [FrameElt(next,(self.segment.psi**(self.Fplus-i)*lifted_rho_coeffs[i]).reduce(),0) for i in range(len(lifted_rho_coeffs))]
            phi_elt = FrameElt(next,self.segment.frame.Ox(1),1)
            next_phi_tail = sum([phi_elt**(self.segment.Eplus*i)*lifted_rho_coeffs_with_psi[i] for i in range(len(lifted_rho_coeffs_with_psi)-1)])
            next_phi = (phi_elt**(self.segment.Eplus*self.Fplus)+next_phi_tail).polynomial()
            self.reduce_elt = FrameElt(next)+(-next_phi_tail) # that is -next_phi_tail
            next.seed(next_phi,length=length)
        return next
