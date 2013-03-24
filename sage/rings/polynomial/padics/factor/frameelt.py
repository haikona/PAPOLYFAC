r"""
Representations of polynomials as sums of powers of OM approximations

A FrameEltTerm object represents a coefficient polynomial multiplied by the
approximation ``phi`` from the previous term.  In the first term, ``phi``
is replaced by the uniformizer, presening a valuation-unit representation
of a constant. The coefficient in FrameEltTerms beyond the first is a
FrameElt from the previous Frame.

A FrameElt is a polynominal in the current Frame as a sum of powers of the
current approximation multiplied by polynomial coefficients.. The
representation is a list of FrameEltTerms, each with a power of the
approximation and coefficient polynomial.

AUTHORS:

- Brian Sinclair (2012-02-22): initial version

"""

class FrameElt:
    """
    Polynomials recursively represented by powers of the approximations
    $\phi_t(x)$ to a factor of $\Phi(x)$.

    INPUT:

    - ``frame`` -- The frame (and thus approximation) this refers to.

    - ``a`` -- Polynomial, default None; The polynomial to be represented
      by self.

    - ``this_exp`` -- Integer, default None; If ``this_exp`` is not None,
      then self is initialized as having a single term in its sum, namely
      ``a`` * ``phi`` ^ ``this_exp``

    EXAMPLES::

    If the FrameElt comes from the first frame, the term must be a constant::

        sage: from sage.rings.polynomial.padics.factor.frame import Frame
        sage: k = ZpFM(2,20,'terse'); kx.<x> = k[]
        sage: f = Frame(x^32+16); f.seed(x)
        sage: FrameElt(f,6)
        [FET<pi^1*3 + O(2^20)>]

    Otherwise the we have an error (from FrameEltTerm)::

        sage: FrameElt(f,x+1)
        Traceback (most recent call last):
        ...
        TypeError: not a constant polynomial

    Moving to a higher frame and representing 6x^2 + 1.  Notice that the
    first FrameEltTerm represents 1 and the second (3 * 2^1)*x^2::

        sage: f = f.polygon[0].factors[0].next_frame(); f
        Frame with phi (1 + O(2^20))*x^8 + (1048574 + O(2^20))
        sage: FrameElt(f,6*x^2 + 1)
        [FET<0,[FET<pi^0*1 + O(2^20)>]>, FET<2,[FET<pi^1*3 + O(2^20)>]>]

    """

    def __init__(self,frame,a=None,this_exp=None):
        """
        Initializes self.

        See ``FrameElt`` for full documentation.

        """
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
            # Compute the phi-expansion of a
            if self.frame.prev_frame().phi.degree() > a.degree():
                b = [a]
            else:
                b = []
                q, r = a.quo_rem(self.frame.prev_frame().phi)
                b.append(r)
                while q != 0:
                    q, r = q.quo_rem(self.frame.prev_frame().phi)
                    b.append(r)
            self.rep = [FrameEltTerm(self,b[i],i) for i in range(len(b)) if b[i].is_zero() == False]

    def is_single_term(self):
        """
        Returns ``True`` if the FrameElt is a sum of only one term, otherwise ``False``

        EXAMPLES::

        """
        if len(self.rep) == 1:
            if self.frame.prev == None:
                return True
            else:
                return self.rep[0]._coefficient.is_single_term()
        return False

    def valuation(self,purge=True):
        """
        Returns the valuation of self

        EXAMPLES::

        """
        if not purge:
            return min([a.valuation() for a in self.rep])
        else:
            if self.rep == []:
                return self.frame.O.precision_cap()
            v = min([a.valuation() for a in self.rep])
            self.rep = [a for a in self.rep if a.valuation() == v]
            return v

    def residue(self):
        """
        Returns the residue of self

        EXAMPLES::

        """
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
        """
        Uses identities to fix the exponents of self to between
        zero and E+ times F+.

        EXAMPLES::

        """
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

    def is_reduced(self):
        """
        Returns ``True`` if all the exponents of all terms are less
        than E+, otherwise ``False``.

        EXAMPLES::

        """
        return all([a.is_reduced() for a in self.rep])

    def find_denominator(self):
        """
        Returns the lowest power (possibly most negative power) of the
        uniformizer in self.

        EXAMPLES::

        """
        if self.frame.is_first():
            return self.rep[0]._exponent
        else:
            return min([fet._coefficient.find_denominator() for fet in self.rep])

    def polynomial(self,denominator=False):
        """
        Returns ``self`` as a polynomial, optionally with the power of the
        uniformizer present in its denominator.

        INPUT:

        - ``denominator`` -- Boolean, default False.  If True, returns the
          polynomial of ``self`` multiplied by the uniformizer to the highest
          power it appears in the denominator of ``self`` and that power as
          a tuple.

        OUTPUT:

        - If ``denominator`` is False, ``self`` as a polynomial.

        - If ``denominator`` is True, returns the tuple of ``self`` multiplied
          to not have a denominator and the power of the uniformizer required
          to clear the denominator.

        EXAMPLES::

        """
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
        # For using sum() command, must be able to be added to int(0)
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
        """
        Raise ``self`` to the integer power ``n``.

        Only single term FrameElts with single terms in all recursive FrameElts
        and FrameEltTerms can be raised this way.

        EXAMPLES::

        Building the needed framework and squaring 6 as a FrameElt::

            sage: from sage.rings.polynomial.padics.factor.frame import Frame
            sage: k = ZpFM(2,20,'terse'); kx.<x> = k[]
            sage: f = Frame(x^32+16); f.seed(x)
            sage: fe = FrameElt(f,6); fe
            [FET<pi^1*3 + O(2^20)>]
            sage: fe.polynomial()
            6 + O(2^20)
            sage: fe.__pow__(2)
            [FET<pi^2*9 + O(2^20)>]
            sage: fe ** 2
            [FET<pi^2*9 + O(2^20)>]
            sage: (fe**2).polynomial()
            36 + O(2^20)

        Moving to a higher frame and squaring 6x^2 as a FrameElt::

            sage: f = f.polygon[0].factors[0].next_frame()
            sage: fe = FrameElt(f,6*x**2);fe  
            [FET<2,[FET<pi^1*3 + O(2^20)>]>]
            sage: fe.polynomial()
            (6 + O(2^20))*x^2
            sage: fe.__pow__(2)                          
            [FET<4,[FET<pi^2*9 + O(2^20)>]>]
            sage: fe**2        
            [FET<4,[FET<pi^2*9 + O(2^20)>]>]
            sage: (fe**2).polynomial()
            (36 + O(2^20))*x^4

        As soon as we are past the first frame, we must take care not to
        try to take powers of non-single-term FrameElts::

            sage: fe = FrameElt(f,6*x^2+1); fe
            [FET<0,[FET<pi^0*1 + O(2^20)>]>, FET<2,[FET<pi^1*3 + O(2^20)>]>]
            sage: fe ** 2
            Traceback (most recent call last):
            ...
            NotImplementedError: Cannot take a power of a non-single term FrameElt

        """
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

    def __getitem__(self,item):
        return self.rep[item]

    def __repr__(self):
        return repr(self.rep)

class FrameEltTerm:
    """
    A single term of the sum of powers of OM representations.

    A FrameEltTerm object should be generated and manipulated by a parent
    FrameElt to which is belongs.

    If the parent FrameElt belongs to the first frame, the FrameEltTerm
    holds a constnat, namely a * pi ^ e.  For frames beyond the first,
    a FrameEltTerm contains the exponent of the previous approximation
    and a FrameElt of the previous frame as a coefficient.

    INPUT:

    - ``frelt`` -- FrameElt. The sum to which this term belongs.

    - ``a`` -- The coefficient of this term.

    - ``e`` -- The exponent of this term.

    EXAMPLES::

    If the parent FrameElt comes from the first frame, the term is a constant::

        sage: from sage.rings.polynomial.padics.factor.frame import Frame
        sage: k = ZpFM(2,20,'terse'); kx.<x> = k[]
        sage: f = Frame(x^32+16); f.seed(x)
        sage: elt = FrameElt(f)
        sage: FrameEltTerm(elt,3,2)
        FET<pi^2*3 + O(2^20)>

    If the uniformizer divides a constant, the FrameEltTerm corrects the exponent::

        sage: FrameEltTerm(elt,6,0)
        FET<pi^1*3 + O(2^20)>
        sage: FrameEltTerm(elt,4,0)
        FET<pi^2*1 + O(2^20)>

    Moving to a higher frame and representing 6x^2 (or 6 * phi ^ 2)::

        sage: f = f.polygon[0].factors[0].next_frame(); f
        Frame with phi (1 + O(2^20))*x^8 + (1048574 + O(2^20))
        sage: elt = FrameElt(f)
        sage: FrameEltTerm(elt,6,2)
        FET<2,[FET<pi^1*3 + O(2^20)>]>
        sage: FrameElt(f,6*x^2)[0]
        FET<2,[FET<pi^1*3 + O(2^20)>]>

    """
    def __init__(self,frelt,a,e):
        """
        Initializes self.

        """
        self.frameelt = frelt
        self._scalar_flag = (self.frameelt.frame.prev == None)
        self._exponent = e
        self._cached_valuation = None
        self._zero_flag = False

        if a in self.frameelt.frame.Ox or a in self.frameelt.frame.O:
            if isinstance(a,int):
                a = self.frameelt.frame.Ox(a)
            self._zero_flag = a.is_zero() #cannot be replaced by a == 0
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
        """
        Returns the valuation of self

        EXAMPLES::
    
        """
        if self._cached_valuation == None:
            if self.frameelt.frame.prev == None:
                self._cached_valuation = self._exponent
            else:
                self._cached_valuation = self.frameelt.frame.prev.segment.slope * self._exponent + self._coefficient.valuation()
        return self._cached_valuation

    def reduce(self):
        """
        Uses identities to fix the exponent of self to be less than
        E+ times F+.

        EXAMPLES::

        """
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
        """
        Returns ``True`` if all the exponents of all terms are less
        than E+, otherwise ``False``.

        EXAMPLES::

        """
        if self.frameelt.frame.prev == None:
            return True
        if self._exponent < self.frameelt.frame.prev.segment.Eplus:
            return self._coefficient.is_reduced()
        return False

    def is_scalar(self):
        """
        Returns ``True`` if the term is just a scalar, otherwise ``False``.

        EXAMPLES::

        """
        return self._scalar_flag

    def is_zero(self):
        """
        Returns ``True`` if the term is equal to 0, otherwise ``False``.

        EXAMPLES::

        """
        return self._zero_flag

    def is_single_term(self):
        """
        Returns ``True`` if the term is does not have more than one term
        at any recursive level, otherwise ``False``.

        EXAMPLES::

        """
        if self._scalar_flag:
            return True
        else:
            return self._coefficient.is_single_term()

    def value(self):
        """
        Returns the coeffecient part of the term.  For scalars, this is a
        single number.  For polynomials, this is the FrameElt representing
        the polynomial coefficient.

        EXAMPLES::

        """
        if self._scalar_flag:
            return self._unit
        else:
            return self._coefficient

    #def __add__(self,right):
    #def __mul__(self,right):
    #    We don't add or multiply on FrameEltTerms directly -- the parent FrameElt does this

    def __pow__(self,n):
        """
        Raise ``self`` to the integer power ``n``.

        Only FrameEltTerms with single terms in all recursive FrameElts
        and FrameEltTerms can be raised this way.

        EXAMPLES::

        Building the needed framework and squaring 12 as a FrameEltTerm::

            sage: from sage.rings.polynomial.padics.factor.frame import Frame
            sage: k = ZpFM(2,20,'terse'); kx.<x> = k[]
            sage: f = Frame(x^32+16); f.seed(x)
            sage: fet = FrameEltTerm(FrameElt(f),3,2); fet
            FET<pi^2*3 + O(2^20)>
            sage: fet.__pow__(2)
            FET<pi^4*9 + O(2^20)>
            sage: fet**2        
            FET<pi^4*9 + O(2^20)>

        Moving to a higher frame and squaring 12x^2 as a FrameEltTerm::

            sage: f = f.polygon[0].factors[0].next_frame()
            sage: fet = FrameEltTerm(FrameElt(f),12,2); fet
            FET<2,[FET<pi^2*3 + O(2^20)>]>
            sage: fet.__pow__(2)                          
            FET<4,[FET<pi^4*9 + O(2^20)>]>
            sage: fet**2        
            FET<4,[FET<pi^4*9 + O(2^20)>]>

        Starting at a depth of 2, we must take care not to try to take
        powers of non-single-term FrameEltTerms::

            sage: f = f.polygon[0].factors[0].next_frame()
            sage: f = f.polygon[0].factors[0].next_frame()
            sage: f.depth
            2
            sage: fet = FrameElt(f,x+1)[0]; fet
            FET<0,[FET<0,[FET<pi^0*1 + O(2^20)>]>, FET<1,[FET<pi^0*1 + O(2^20)>]>]>
            sage: fet ** 2 # Error
            Traceback (most recent call last):
            ...
            NotImplementedError: Cannot take a power of a non-single term FrameEltTerm

        """
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
        """
        Return the negative of ``self``.

        OUTPUT: FrameEltTerm

        EXAMPLES::

            sage: from sage.rings.polynomial.padics.factor.frame import Frame
            sage: k = ZpFM(2,20,'terse'); kx.<x> = k[]
            sage: f = Frame(x^32+16); f.seed(x)
            sage: f = f.polygon[0].factors[0].next_frame();
            sage: elt = FrameElt(f)
            sage: fet = FrameEltTerm(elt,6,2); fet
            FET<2,[FET<pi^1*3 + O(2^20)>]>
            sage: FrameElt(f,6*x^2)[0]
            FET<2,[FET<pi^1*3 + O(2^20)>]>
            sage: fet.__neg__()
            FET<2,[FET<pi^1*524285 + O(2^20)>]>
            sage: -fet
            FET<2,[FET<pi^1*524285 + O(2^20)>]>
            sage: FrameElt(f,-6*x**2)[0]             
            FET<2,[FET<pi^1*524285 + O(2^20)>]>

        """
        if self.frameelt.frame.is_first():
            return FrameEltTerm(self.frameelt,-self._unit,self._exponent)
        else:
            return FrameEltTerm(self.frameelt,-self._coefficient,self._exponent)

    def __repr__(self):
        """
        Representation of self.

        """
        if self._zero_flag:
            return 'FET<0>'
        if self._scalar_flag:
            return 'FET<pi^'+repr(self._exponent)+'*'+repr(self._unit)+'>'
        else:
            return 'FET<'+repr(self._exponent)+','+repr(self._coefficient)+'>'
