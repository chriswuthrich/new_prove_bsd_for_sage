r"""
This is a new attempt to implement prove_BSD function for elliptic curves
defined over Q.
The name is also debatable, since it returns a list of primes where
it cannot prove it.

Here the sage issue : https://github.com/sagemath/sage/pull/42397
and the one for the lmfdb: https://github.com/LMFDB/lmfdb/issues/7045

Issues:
* We have to check if all is proven. sha.an needs the Manin constant to be 1 or 2.
* Should check if L>0 for full BSD.
* Find more resources, decide if unpublished preprints are ok.
* Should we check an=rank for rank 2 and 3 curves?
* cm an=1 case
* check what needs caching to avoid recalculation

Preliminary list of references:
[BSTW] Ashay Burungale, Christopher Skinner, Ye Tian, Xin Wan, Zeta elements for elliptic curves and applications, https://arxiv.org/abs/2409.01350, unpublished
[BT] Ashay A. Burungale, Ye Tian, A rank zero p-converse to a theorem of Gross--Zagier, Kolyvagin and Rubin, https://arxiv.org/abs/2506.03465, Annals of Maths
[R] Karl Rubin,The 'main conjectures' of Iwasawa theory for imaginary quadratic fields., https://eudml.org/doc/143852, Inventiones mathematicae (1991) Volume: 103, Issue: 1, page 25-68
[CGLS] Francesc Castella, Giada Grossi, Jaehoon Lee, Christopher Skinner, On the anticyclotomic Iwasawa theory of rational elliptic curves at Eisenstein primes, https://arxiv.org/abs/2008.02571, Invent. Math. 227 (2022), no. 2, 517–580.
[CGS] Francesc Castella, Giada Grossi, Christopher Skinner, Mazur's main conjecture at Eisenstein primes, https://arxiv.org/abs/2303.04373, Math. Ann. 393 (2025), no. 2, 2451–2506.
[K] Kazuya Kato,
[C] Francesc Castella, On the p-part of the Birch-Swinnerton-Dyer formula for multiplicative primes. Camb. J. Math. 6 (2018), no. 1, 1–23. With erratum at https://web.math.ucsb.edu/~castella/Birch-erratum.pdf
[BCS] Ashay Burungale, Francesc Castella, Christopher Skinner, Base change and Iwasawa main conjectures for  GL2 , Int. Math. Res. Not. IMRN 2025, no. 8, Paper No. rnaf082, 15 pp.

[KY]  Timo Keller, Mulun Yin, On the anticyclotomic Iwasawa theory of newforms at Eisenstein primes of semistable reduction, https://arxiv.org/abs/2402.12781, unpublished and I trust it less
[FW] Olivier Fouquet, Xin Wan, The Iwasawa Main Conjecture for universal families of
modular motives,  https://arxiv.org/pdf/2107.13726, not yet published and
harder to make explicit, but it would cover additive cases when an=0.
"""

from sage.all import *

# from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ


# note I only use pari-gp, not mwrank or sage's own slow implementation of the
# two-descent. The reason is that pari also calculates the Cassels-Tate
# pairing that is helpful (and did not seem to have been used before).
def _new_prove_bsd_2(E, an, verbosity=0):
    """
    Check BSD(E,2) using the two-descent.
    This function is only called if the analytic rank is <= 1
    and that must be equal to the argument ``an``.

    Returns a boolean, which is True if BDS(E,2) is proven, and a list of points.
    """
    if an > 1:
        raise RuntimeError("This function should only be called if the analytic rank is <= 1.")
    ep = E.pari_curve()
    lower, rank_upper_bd, s, pts = ep.ellrank()
    # this is explained in the pari-gp documentation:
    # s is the dimension of Sha[2]/2Sha[4],
    # which is a lower bound for dim Sha[2]
    if verbosity>1:
        print(f"The two-descent gives the following information: {lower} <= rank <= {rank_upper_bd},"
              f"dim Sha[2]/2Sha[4] = {s} and the following points were found: {pts}.")

    # sanity checks
    if (lower > rank_upper_bd or lower != len(pts) or
        lower > an or rank_upper_bd < an or len(pts) > 1):
        raise RuntimeError(f"The two-descent failed for this curve. "
                           f"The lower bound is {lower} and the upper bound is {rank_upper_bd}. "
                           f"The analytic rank is {an} and we found the following "
                           f"independent points : {pts}.")

    # Not sure if we need the point later
    if len(pts) == 1:
        gens = [ E.point([ QQ(pts[0][0]), QQ(pts[0][1]) ], check=True) ]
        gens = E.saturation(gens)[0]
    else:
        gens = []

    # We know by Kolyvagin-Gross-Zagier that the rank is equal to the analytic rank.
    rank = an

    # this is the dimension of Sha[2]
    sel2 = rank_upper_bd + s - rank
    if sel2 == s:
        # this implies that 2Sha[4]=0 and hence Sha[4] = Sha[2] is all of the 2-primary
        # part of Sha
        if sel2 == E.sha().an().ord(2):
            if verbosity>0:
                print(f"BSD(E,2) holds thanks to a 2-descent calculation.")
            return True, gens
        else:
            print(f"It appears that BSD(E,2) does not holds for this curve. "
                  f"This is either a counterexample to BSD or, more likely, a bug. "
                  f"The dimension of Sha[2] is {sel2}, which must be all of Sha[2^oo], "
                  f"but the analytic order of Sha is {E.sha().an()}.")
            return False, gens
    else:
        # in this case Sha[4] is non-trivial. We cannot determine
        # the order of Sha[2^oo] and we cannot conclude if BSD(E,2) holds.
        if verbosity>1:
            print(f"We cannot conclude that BSD(E,2) holds using a 2-descent. "
                  f"The 2-primary part of Sha contains at least {2**(2*sel2-s)} elements "
                  f"and the analytic order of Sha is {E.sha().an()}.")
        return False, gens


# currently (July 2026) still unpublished
def burungale_skinner_tian_wan_thm19(E, p, verbosity=0):
    """
    Check if the conditions of Theorem 1.9 in [BSTW]
    If so BDS(E,p) holds.
    """
    rho = E.galois_representation()
    if p == 2:
        return False
    elif E.conductor()%p == 0:
        return False
    elif rho.is_reducible(p):
        return False
    # now E[p] is irreducible. If E is defined over Q
    # this implies that E[p] is absolutely irr
    # since the image cannot be in a non-split Cartan.
    elif E.is_supersingular():
        return False
    else:
        ells = [ell for ell in E.conductor().prime_divisors() if E.conductor() % (ell**2) != 0]
        useful_ells = [ell for ell in ells if E.j_invariant().valuation(ell) % p != 0]
        if len(useful_ells) == 0:
            return False
        else:
            an = E.analytic_rank()
            if an == 1:
                if verbosity>0:
                    print(f"Theorem 1.9 in [BSTW] with ell in {useful_ells} proves BSD(E,{p}).")
                return True
            else:
                return False


# currently (July 2026) still unpublished
def burungale_skinner_tian_wan_thm15(E,p, verbosity=0):
    """
    Check if the conditions of Theorem 1.5 in [BSTW]
    is so BDS_p(E) holds.
    """
    rho = E.galois_representation()
    if p == 2:
        return False
    elif E.conductor()%p == 0:
        return False
    elif rho.is_ordinary(p):
        return False
    else:
        if p==3 and E.ap(p)!=0:
            return False
        else:
            if E.analytic_rank() <= 1:
                if verbosity>1:
                    print(f"Theorem 1.5 in [BSTW] proves BSD(E,{p}).")
                return True
            else:
                return False

# multiplicative case
def castella_thmAprime(E, p, verbosity=0):
    """
    Check if the conditions of Theorem A' in the erratum to [C]
    are verified.
    """
    if p==2:
        return False
    elif not E.has_multiplicative_reduction(p):
        return False
    elif not E.galois_representation().is_irreducible(p):
        return False
    elif has_padic_ptorsion_point(E,p):
        return False
    elif E.analytic_rank() != 1:
        return False
    else:
        qs = [q for q in E.conductor().prime_divisors() if E.has_non_split_multiplicative_reduction(q) and q!=p]
        if len(qs)==0:
            return False
        boo = any(E.j_invariant().valuation(q)%p!=0 for q in qs) # check if E[p] is ramified at one q
        if boo and verbosity>0:
            print(f"Theorem A' in [C] proves BSD(E,{p})"
                  f"using the auxiliary primes {[q for q in qs if E.j_invariant().valuation(q)%p!=0]}.")
        return boo


# ---------------- reducible cases --------------

def has_padic_ptorsion_point(E, p):
    """
    Return True if E(Q_p) contains a p-torsion point.
    Implemented for p>2.
    """
    p = ZZ(p)
    from sage.rings.polynomial.polynomial_ring import PolynomialRing_dense_padic_field_capped_relative as PRing
    R = Qp(p,30)
    RX = PRing(R, "X")
    if p == 2:
        # this is harder as it could have torsion in the formal group
        raise NotImplementedError("Not implemented for p=2.")
    elif p == 3:
        f = RX(E.division_polynomial(3))
        ro = f.roots()
        if len(ro)==0:
            return False
        else:
            Ep = E.change_ring(R)
            return any(Ep.is_x_coord(xx[0]) for xx in ro)
    elif E.has_split_multiplicative_reduction(p):
        # has p-torsion iff q is a p-th power
        q = E.tate_curve(p).parameter()
        if q.valuation() % p != 0:
            return False
        else:
            u = q/p**(q.valuation()/p) # a unit
            f = RX.gens()[0] ** p - u
            return len(f.roots())>1
    elif (not E.has_additive_reduction(p)) and E.Np(p)%p != 0:
        # now the group of components has order coprime to p
        # the reduction has no p-torsion -> no p-torsion over Qp
        # non-split mult drops here
        return False
    else:
        Ep = E.change_ring(R)
        if E.has_good_reduction(p):
            Ptilda = next(P for P in E.reduction(p) if P.order()==p)
            xx = R(ZZ(Ptilda[0]))
            P = Ep.lift_x(xx)
            Q = p*P
        else:
            # must have additive reduction
            # any non-singular point has order p
            for xx in srange(p):
                if Ep.is_x_coord(R(xx)):
                    P = Ep.lift_x(R(xx))
                    Q = p*P
                    if Q[0].valuation() < 0:
                        break
        if Q[0].valuation() < -2:
            return True
        else:
            return False
        # Explanation: We use the exact sequence
        # 0->E(Qp)[p] -> G[p] -> Ehat(pZp)/p
        # where G is the quotient of E(Qp) by the
        # kernel of reduction Ehat(pZp)
        # above we test if a non-trivial element of G
        # maps to zero.


def castella_grossi_lee_skinner_thmf(E, p, verbosity=0):
    """
    Check if the conditions of Theorem F in [CGLS] hold
    if so BDS_p(E) holds.
    """
    if p == 2:
        return False
    elif E.galois_representation().is_irreducible(p):
        return False
    elif E.torsion_order()%p == 0:
        return False
    elif E.analytic_rank() > 2:
        return False
    else:
        # check if phi|G_Qp is 1 or omega:
        if has_padic_ptorsion_point(E,p):
            return False
        phis = E.isogenies_prime_degree(p)
        assert( len(phis)>0 )
        Cs = [phi.codomain() for phi in phis]
        if any(has_padic_ptorsion_point(C,p) for C in Cs):
            return False
        for phi in phis:
            c = phi.scaling_factor()
            # ramified if c=p unramified if c=1
            ro = phi.kernel_polynomial().change_ring(RR).roots()
            xx = ro[0][0]
            boo = E.change_ring(RR).is_x_coord(xx)
            # ker phi is even iff boo (the kernel has real points)
            if (c==1 and boo) or (c==p and not boo):
                if verbosity>0:
                    print(f"Theorem F in [CGLS] proves BSD(E,{p}).")
                return True
        return False

def castella_grossi_skinner_thmd(E, p , verbosity=0):
    """
    Check if the coditions in Theorem D in [CGS] hold
    If so BDS_p(E) holds.
    """
    if p==2:
        return False
    elif E.galois_representation().is_irreducible(p):
        return False
    elif E.analytic_rank() > 1:
        return False
    elif E.conductor()%p == 0:
        return False
    else:
        # check if phi|G_Qp is 1 or omega:
        if has_padic_ptorsion_point(E,p):
            return False
        phis = E.isogenies_prime_degree(p)
        assert( len(phis)>0 )
        Cs = [phi.codomain() for phi in phis]
        if any(has_padic_ptorsion_point(C,p) for C in Cs):
            return False
        else:
            if verbosity>0:
                print(f"Theorem D in [CGS] proves BSD(E,{p}).")
            return True

# currently (July 2026) unpublished preprint, strictly stronger than castella_grossi_lee_skinner_thmf
def keller_yin_thmc(E, p, verbosity=0):
    """
    Check if the conditions of Theorem C in [KY] hold
    if so BDS_p(E) holds.
    """
    if p == 2:
        return False
    elif E.galois_representation().is_irreducible(p):
        return False
    elif E.analytic_rank() > 1:
        return False
    else:
        if verbosity>0:
            print(f"Theorem C in [KY] proves BSD(E,{p}).")
        return True

# ---------------- cm case --------------

def _new_prove_bsd_cm(E, verbosity=0):
    non_max_j_invs = [ -12288000, 54000, 287496, 16581375 ]
    if E.j_invariant() in non_max_j_invs:
        if verbosity > 0:
            print('CM by non maximal order: switching curves.')
        E2 = next(C for C in E.isogeny_class().curves if C.j_invariant() not in non_max_j_invs)
    else:
        E2 = E
    an = E2.analytic_rank()
    attwo, _ = _new_prove_bsd_2(E2, an, verbosity=verbosity)
    if an == 0:
        # by the first main Theorem in Rubin's 1991 [R] article The "main conjectures" of Iwasawa theory for imaginary quadratic fields.
        # only primes diving the order of the units in End
        res = [] if attwo else [2]
        if E2.j_invariant() == 0:
            res.append(3)
            if verbosity>0:
                print(f"Rubin's theorem in [R] proves BSD(E,p) for all p>3.")
        elif verbosity>0:
            print(f"Rubin's theorem in [R] proves BSD(E,p) for all p>2.")
        return res
    elif an == 1:
        return NotImplementedError("This is not implemented yet.")
    else: # an> 1
        # We should not be calling this function for curves with analytic rank > 1.
        # This is a bug.
        raise RuntimeError("Called _new_prove_bsd_cm with a curve of analytic rank > 1. This is a bug.")


# -----------------
# the main function
#------------------

def new_prove_bsd(E,
                  verbosity=0):
    r"""
    Attempt to prove the Birch and Swinnerton-Dyer conjectural
    formula for `E`, returning a list of primes `p` for which this
    function fails to prove BSD(E,p).

    Here, BSD(E,p) is the
    statement: "the Birch and Swinnerton-Dyer formula holds up to a
    rational number coprime to `p`."

    INPUT:

    - ``E`` -- an elliptic curve

    - ``verbosity`` -- integer; how much information about the proof to print

      - 0: print nothing
      - 1: print sketch of proof
      - 2: print information about remaining primes

    """
    # no hope to prove anything if analytic rank is >1
    an = E.analytic_rank()
    if an > 1:
        from sage.sets.primes import Primes
        if verbosity > 0:
            print(f"Cannot verify BSD(E,p) for any prime p as the analytic rank is > 1.")
        return Primes()

    # first treat CM curves
    if E.has_cm():
        return _new_prove_bsd_cm(E, verbosity=verbosity)

    # now curve is not cm
    # bsd_p is invariant under isogeny.
    # the best curve in the isoclass is the one with the smallest analytic order of sha.
    E2 = min(E.isogeny_class().curves, key=lambda C: C.sha().an())
    attwo, gens = _new_prove_bsd_2(E2, an, verbosity=verbosity)
    # resulting list of primes is stored in res
    res = [] if attwo else [2]

    if an == 0:
        # we know that BSD(E,p) holds if Kato's thm 14.5 holds
        # and the analytic order of sha is not
        # divisible by p
        # Kato's theorem [K] 14.5 requires p>2, potentially good reduction and
        # surjectivity of the representation on E[p]
        primes_to_test = Set(E2.galois_representation().non_surjective())
        primes_to_test += Set(E2.sha().an().prime_divisors())
        primes_to_test += Set(E2.j_invariant().denominator().prime_divisors())
        primes_to_test = primes_to_test.difference(Set([2]))
    else: # an == 1
        raise NotImplementedError("")

    if verbosity > 1:
        print(f"Primes left to test: {primes_to_test}")

    for p in primes_to_test:
        # is any of the criteria above apply, go to the next prime
        # otherwise append it to the result in res
        if not any([
            burungale_skinner_tian_wan_thm19(E, p, verbosity=verbosity), #unpublished
            burungale_skinner_tian_wan_thm15(E, p, verbosity=verbosity), #unpublished
            castella_grossi_lee_skinner_thmf(E, p, verbosity=verbosity),
            keller_yin_thmc(E, p, verbosity=verbosity), # unpublished
            castella_thmAprime(E, p , verbosity=verbosity),
            castella_grossi_skinner_thmd(E, p , verbosity=verbosity)
        ] ):
            res.append(p)

    # give extra information if verbosity is 2
    if verbosity > 1 and len(res)>0 and an<=1:
        print(f"BSD(E,p) is not known to hold for the primes {res}.")
        print(f" E has analytic and algebraic rank {an}.")
        if E.has_cm():
            print(f" E has complex multiplication with discriminant {E.cm_discriminant()}.")
        tam = ""
        for ell in E.conductor().prime_divisors():
            tam += f"c_{ell} = {E.tamagawa_number(ell)}, "
        tam = tam[:-2] # delete trailing ",2
        print(f" The Tamagawa numbers are {tam}.")
        print(f" The torsion order is {E.torsion_order()}.")
        for p in res:
            if E.has_good_reduction(p):
                if E.ap(p)%p == 0:
                    redstr = f"supersingular reduction with a_p={E.ap(p)}"
                else:
                    if E.Np(p)%p == 0:
                        redstr = f"good ordinary anomalous reduction"
                    else:
                        redstr = f"good ordinary non-anomalous reduction"
            elif E.has_split_multiplicative_reduction(p):
                redstr = f"split multiplicative reduction"
            elif E.has_nonsplit_multiplicative_reduction(p):
                redstr = f"non-split multiplicative reduction"
            else:
                redstr = f"additive multiplicative reduction"
            print(f" * At {p=}, the curve has {redstr}.")
            if E.galois_representation().is_irreducible(p):
                if E.galois_representation().is_surjective(p):
                    print(f"   The Galois representation on E[{p}] is surjective.")
                else:
                    print(f"   The Galois representation E[{p}] is irreducible, but not surjective.")
            else:
                print(f"   The Galois representation E[{p}] is reducible.")

    return res


if __name__ == "__main__":
    for la in ['11a', '14a', '20a1', '50b1', '389a',
               '19a', '37a', '123a1', '681b', '198b',
               '26b', '438e1', '960d1', '66b3']:
        E = EllipticCurve(la)
        print(f"Curve: {E.label()} \n old prove_BSD :: {E.prove_BSD()} \n")
        if E.analytic_rank() == 0:
            print(f"{new_prove_bsd(E, 2)}")
        elif E.analytic_rank() == 1:
            print(f"{_new_prove_bsd_2(E, E.analytic_rank(), verbosity=2)}\n")
        print("\n")
    print("Done.")