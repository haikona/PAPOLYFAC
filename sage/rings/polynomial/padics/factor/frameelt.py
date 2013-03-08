class FrameElt:
    """Polynomials recursively represented by powers of the approximations $\phi_t(x)$ to a factor of $\Phi(x)$."""

    def __init__(self,frame,a=None,this_exp=None):
        # deg(a) < deg(frame.phi)*frame.Eplus*frame.Fplus
        self.frame = frame
        if this_exp != None:
            # initializes a FrameElt of phi_t ^ this_exp * a
            self.rep = [FrameEltTerm(self,a,this_exp)]
        elif a == None:
            self.rep = []
        elif frame.is_first():
            self.rep = [FrameEltTerm(self,a,0)]
        else:
            b = _phi_expansion(a,self.frame.prev_frame().phi)
            self.rep = [FrameEltTerm(self,b[i],i) for i in range(len(b)) if b[i].is_zero() == False]

    def is_single_term(self):
        if len(self.rep) == 1:
            if self.frame.prev == None:
                return True
            else:
                return self.rep[0]._coefficient.is_single_term()
        return False

    def valuation(self,purge=True):
        if not purge:
            return min([a.valuation() for a in self.rep])
        else:
            if self.rep == []:
                return self.frame.O.precision_cap()
            v = min([a.valuation() for a in self.rep])
            self.rep = [a for a in self.rep if a.valuation() == v]
            return v

    def residue(self):
        if not self.is_reduced():
            self = self.reduce()

        if self.frame.is_first():
            if self.rep[0]._exponent == 0:
                # unable to coerce in Zq
                return self.frame.R(self.rep[0]._unit)
            else:
                return self.frame.R(0)

        Eplus = int(self.frame.prev.segment.Eplus)
        if self.frame.prev.Fplus > 1:
            psi = self.frame.prev.segment.psi
            gamma = self.frame.prev.gamma
            residuelist = [gamma**(a._exponent/Eplus)*self.frame.prev.FFbase_elt_to_FF((psi**(a._exponent/Eplus)*a.value()).residue()) for a in self.rep if int(a._exponent) % Eplus == 0]
        else:
            residuelist = [a.value().residue() for a in self.rep if int(a._exponent) == 0]
        if len(residuelist) > 0:
            return sum(residuelist)
        else:
            return self.frame.R(0)

    def reduce(self):
        if self.frame.is_first():
            return self
        Eplus = self.frame.prev.segment.Eplus
        Fplus = self.frame.prev.Fplus
        reduced_elt = FrameElt(self.frame) # zero FrameElt
        for a in self.rep:
            if a._exponent >= Eplus * Fplus:
                b = FrameElt(self.frame)
                b.rep = [FrameEltTerm(b,a.value(),a._exponent - Eplus * Fplus)]
                b *= self.frame.prev.reduce_elt
                reduced_elt += b.reduce()
            elif a._exponent < 0:
                b = FrameElt(self.frame)
                b.rep = [FrameEltTerm(b,a.value(),a._exponent + Eplus * Fplus)]
                b *= (self.frame.prev.reduce_elt)**(-1)
                reduced_elt += b.reduce()
            else:
                summand = FrameElt(self.frame)
                summand.rep = [FrameEltTerm(reduced_elt,a.value().reduce(),a._exponent)]
                reduced_elt += summand
        return reduced_elt

    def sumcollapse(self):
        sumt = FrameElt(self.frame)
        sumc = FrameElt(self.frame)
        for i in range(len(self.rep)):
            sumc.rep = [self.rep[i]]
            sumt += sumc
        return sumt

    def is_reduced(self):
        return all([a.is_reduced() for a in self.rep])

    def find_denominator(self):
        """
        Find the lowest power (possibly negative) of the uniformizer in a FrameElt
        """
        if self.frame.is_first():
            return self.rep[0]._exponent
        else:
            return min([fet._coefficient.find_denominator() for fet in self.rep])

    def polynomial(self,denominator=False):
        if denominator:
            piexp = self.find_denominator()
            if piexp < 0:
                return (self * FrameElt(self.frame,self.frame.Ox(self.frame.O.uniformizer()**(-piexp)))).polynomial(),-piexp
            else:
                return self.polynomial(),0
        else:
            if self.frame.is_first():
                return self.frame.O.uniformizer()**int(self.rep[0]._exponent)*self.rep[0]._unit
            else:
                return sum([self.frame.prev_frame().phi**int(a._exponent)*a._coefficient.polynomial() for a in self.rep])

    def __neg__(self):
        if self.frame.is_first():
            return FrameElt(self.frame,-self.polynomial())
        else:
            neg = FrameElt(self.frame)
            neg.rep = [-r for r in self.rep]
            return neg

    def __radd__(self,l):
        return self.__add__(l)

    def __add__(self,r):
        if isinstance(r,int) and r == 0:
            return self
        if self.frame.phi != r.frame.phi:
            raise ValueError, "Cannot add FrameElts with different values of phi"
        if len(self.rep) == 0:
            return r
        sum = FrameElt(self.frame)
        if self.frame.prev == None:
            v = min(self.rep[0]._exponent,r.rep[0]._exponent)
            pi = self.frame.O.uniformizer()
            usum = self.rep[0]._unit * pi ** (self.rep[0]._exponent - v)
            usum = usum + r.rep[0]._unit * pi ** (r.rep[0]._exponent - v)
            sum.rep = [FrameEltTerm(sum,usum,v)]
        else:
            if self.rep == []:
                for k in range(len(r.rep)):
                    sum.rep.append(FrameEltTerm(sum,r.rep[k].value(),r.rep[k]._exponent))
            elif r.rep == []:
                for k in range(len(self.rep)):
                    sum.rep.append(FrameEltTerm(sum,self.rep[k].value(),self.rep[k]._exponent))
            else:
                i = 0 ; j = 0
                while i < len(self.rep) and j < len(r.rep):
                    if self.rep[i]._exponent < r.rep[j]._exponent:
                        sum.rep.append(FrameEltTerm(sum,self.rep[i].value(),self.rep[i]._exponent))
                        i = i + 1
                    elif self.rep[i]._exponent > r.rep[j]._exponent:
                        sum.rep.append(FrameEltTerm(sum,r.rep[j].value(),r.rep[j]._exponent))
                        j = j + 1
                    elif self.rep[i]._exponent == r.rep[j]._exponent:
                        sum.rep.append(FrameEltTerm(sum,self.rep[i].value()+r.rep[j].value(),self.rep[i]._exponent))
                        i = i + 1; j = j + 1
                if j < len(r.rep):
                    for k in range(j,len(r.rep)):
                        sum.rep.append(FrameEltTerm(sum,r.rep[k].value(),r.rep[k]._exponent))
                elif i < len(self.rep):
                    for k in range(i,len(self.rep)):
                        sum.rep.append(FrameEltTerm(sum,self.rep[k].value(),self.rep[k]._exponent))
        return sum

    def __rmul__(self,l):
        return self.__mul__(l)

    def __mul__(self,r):
        if isinstance(r,int) and r == 0:
            return self
        if self.frame.depth != r.frame.depth:
            raise ValueError, "Cannot multiply FrameElts with different frame depths"
        product = FrameElt(self.frame)
        if self.frame.prev == None:
            v = self.rep[0]._exponent + r.rep[0]._exponent
            uprod = self.rep[0]._unit
            uprod = uprod * r.rep[0]._unit
            product.rep = [FrameEltTerm(product,uprod,v)]
        else:
            for i in range(len(self.rep)):
                summand = FrameElt(self.frame)
                for j in range(len(r.rep)):
                    summand.rep.append(FrameEltTerm(product,self.rep[i].value()*r.rep[j].value(),self.rep[i]._exponent+r.rep[j]._exponent))
                product = product + summand
        return product

    def __pow__(self,n):
        if not self.is_single_term():
            raise NotImplementedError, "Cannot take a power of a non-single term FrameElt"
        else:
            product = FrameElt(self.frame)
            product.rep = [self.rep[0]**n]
            return product

    def __div__(self,right):
        if not right.is_single_term():
            raise NotImplementedError, "Cannot divide by a non-single term FrameElt"
        else:
            quotient = FrameElt(self.frame)
            quotient.rep = [a / right.rep[0] for a in self.rep]
            return quotient

    def __repr__(self):
        return repr(self.rep)

def _phi_expansion(P,phi):
    """ Compute the phi-expansion of P """
    if phi.degree() > P.degree():
        return [P]
    expansion = []
    q, r = P.quo_rem(phi)
    expansion.append(r)
    while q != 0:
        q, r = q.quo_rem(phi)
        expansion.append(r)
    return expansion

class FrameEltTerm:

    def __init__(self,frelt,a,e):
        self.frameelt = frelt
        self._scalar_flag = (self.frameelt.frame.prev == None)
        self._exponent = e
        self._cached_valuation = None
        self._zero_flag = False

        if a in self.frameelt.frame.Ox or a in self.frameelt.frame.O:
            self._zero_flag = a.is_zero()
            if self._scalar_flag:
                a = self.frameelt.frame.O(a)
                if self._zero_flag:
                    self._unit = a
                else:
                    self._unit = a.unit_part()
                if a.valuation() > 0 and a.valuation():
                    self._exponent += a.valuation()
            else:
                self._coefficient = FrameElt(self.frameelt.frame.prev_frame(),a)
        else:
            self._coefficient = a
            a._zero_flag = False

    def valuation(self):
        if self._cached_valuation == None:
            if self.frameelt.frame.prev == None:
                self._cached_valuation = self._exponent
            else:
                self._cached_valuation = self.frameelt.frame.prev.segment.slope * self._exponent + self._coefficient.valuation()
        return self._cached_valuation

    def reduce(self):
        if self.frameelt.frame.prev == None:
            return
        Eplus = self.frameelt.frame.prev.segment.Eplus
        Fplus = self.frameelt.frame.prev.Fplus

        if self._exponent >= Eplus * Fplus:
            q,r = int(self._exponent).quo_rem(int(Eplus))
            self._exponent = r
            self._coefficient *= (self.frameelt.frame.prev.segment.psi ** (q*Fplus))
        self._coefficient.reduce()
        return

    def is_reduced(self):
        if self.frameelt.frame.prev == None:
            return True
        if self._exponent < self.frameelt.frame.prev.segment.Eplus:
            return self._coefficient.is_reduced()
        return False

    def is_scalar(self):
        return self._scalar_flag
    def is_zero(self):
        return self._zero_flag
    def is_single_term(self):
        if self._scalar_flag:
            return True
        else:
            return self._coefficient.is_single_term()

    def value(self):
        if self._scalar_flag:
            return self._unit
        else:
            return self._coefficient

    #def __add__(self,right):
    #def __mul__(self,right):
    #    We don't add or multiply on FrameEltTerms directly -- the parent FrameElt does this

    def __pow__(self,n):
        if not self.is_single_term():
            raise NotImplementedError, "Cannot take a power of a non-single term FrameEltTerm"
        else:
            n = int(n)
            if self._scalar_flag:
                return FrameEltTerm(self.frameelt, self._unit**n, self._exponent*n)
            else:
                return FrameEltTerm(self.frameelt, self._coefficient**n, self._exponent*n)

    def __div__(self,right):
        if not right.is_single_term():
            raise NotImplementedError, "Cannot divide by a non-single term FrameEltTerm"
        else:
            if self._scalar_flag:
                return FrameEltTerm(self.frameelt, self._unit/right._unit, self._exponent-right._exponent)
            else:
                return FrameEltTerm(self.frameelt, self._coefficient/right._coefficient, self._exponent-right._exponent)

    def __neg__(self):
        if self.frameelt.frame.is_first():
            return FrameEltTerm(self.frameelt,-self._unit,self._exponent)
        else:
            return FrameEltTerm(self.frameelt,-self._coefficient,self._exponent)

    def __repr__(self):
        if self._zero_flag:
            return 'FET<0>'
        if self._scalar_flag:
            return 'FET<pi^'+repr(self._exponent)+'*'+repr(self._unit)+'>'
        else:
            return 'FET<'+repr(self._exponent)+','+repr(self._coefficient)+'>'
