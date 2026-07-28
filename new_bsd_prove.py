
from sage.all import *


# from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ



def _new_prove_bsd_2(E, an, verbosity=0):
    """
    Check BSD(E,2) using the two-descent.
    This function is only called if the analytic rank is <= 1
    and that must be equal to the argument ``an``.

    Returns a boolean, which is True if BDS(E,2) is proven, and a list of points.
    """
    if an > 1:
        raise RuntimeError("This function should only be called if the analytic rank is <= 1")
    ep = E.pari_curve()
    lower, rank_upper_bd, s, pts = ep.ellrank()
    # this is explained in the pari-gp documentation:
    # s is the dimension of Sha[2]/2Sha[4],
    # which is a lower bound for dim Sha[2]
    if verbosity>1:
        print(f"The two-descent gives the following information: {lower} <= rank <= {rank_upper_bd},"
              f"dim Sha[2]/2Sha[4] = {s} and the following points were found: {pts}")

    # sanity checks
    if (lower > rank_upper_bd or lower != len(pts) or
        lower > an or rank_upper_bd < an or len(pts) > 1):
        raise RuntimeError(f"The two-descent failed for this curve. "
                           f"The lower bound is {lower} and the upper bound is {rank_upper_bd}. "
                           f"The analytic rank is {an} and we found the following "
                           f"independent points : {pts}")


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
        if verbosity>0:
            print(f"We cannot conclude that BSD(E,2) holds using a 2-descent. "
                  f"The 2-primary part of Sha contains at least {2**(2*sel2-s)} elements "
                  f"and the analytic order of Sha is {E.sha().an()}.")
        return False, gens



def burungale_skinner_tian_wan_thm19(E, p, verbosity=0):
    """
    Check if the conditions of Theorem 1.9 in

    ZETA ELEMENTS FOR ELLIPTIC CURVES AND APPLICATIONS
    by
    ASHAY A. BURUNGALE, CHRISTOPHER SKINNER, YE TIAN AND XIN WAN

    is so BDS_p(E) holds.
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
                if verbosity>1:
                    print(f"Theorem 1.9 in [BSTW] with ell in {useful_ells} proves BSD(E,{p})")
                return True
            else:
                return False


def burungale_skinner_tian_wan_thm15(E,p, verbosity=0):
    """
    Check if the conditions of Theorem 1.5 in

    ZETA ELEMENTS FOR ELLIPTIC CURVES AND APPLICATIONS
    by
    ASHAY A. BURUNGALE, CHRISTOPHER SKINNER, YE TIAN AND XIN WAN

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
                    print(f"Theorem 1.5 in [BSTW] proves BSD(E,{p})")
                return True
            else:
                return False


def _new_prove_bsd_cm(E, verbosity=0):
    non_max_j_invs = [ -12288000, 54000, 287496, 16581375 ]
    if E.j_invariant() in non_max_j_invs:
        if verbosity > 0:
            print('CM by non maximal order: switching curves')
        E2 = next(C for C in E.isogeny_class().curves if C.j_invariant() not in non_max_j_invs)
    else:
        E2 = E
    an = E2.analytic_rank()
    attwo, _ = _new_prove_bsd_2(E2, an, verbosity=verbosity)
    if an == 0:
        # by the first main Theorem in Rubin's 1991 article The "main conjectures" of Iwasawa theory for imaginary quadratic fields.
        # only primes diving the order of the units in End
        res = [2] if attwo else []
        if E2.j_invariant() == 0:
            res.append(3)
        return res
    elif an == 1:
        return NotImplementedError("This is not implemented yet.")
    else: # an> 1
        # We should not be calling this function for curves with analytic rank > 1.
        # This is a bug.
        raise RuntimeError("Called _new_prove_bsd_cm with a curve of analytic rank > 1. This is a bug.")


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

     EXAMPLES::

        sage: EllipticCurve('11a').prove_BSD(verbosity=2)
        p = 2: True by 2-descent
        True for p not in {2, 5} by Kolyvagin.
        Kolyvagin's bound for p = 5 applies by Lawson-Wuthrich
        True for p = 5 by Kolyvagin bound
        []

        sage: EllipticCurve('14a').prove_BSD(verbosity=2)
        p = 2: True by 2-descent
        True for p not in {2, 3} by Kolyvagin.
        Kolyvagin's bound for p = 3 applies by Lawson-Wuthrich
        True for p = 3 by Kolyvagin bound
        []

        sage: E = EllipticCurve("20a1")
        sage: E.prove_BSD(verbosity=2)
        p = 2: True by 2-descent
        True for p not in {2, 3} by Kolyvagin.
        Kato further implies that #Sha[3] is trivial.
        []

        sage: E = EllipticCurve("50b1")
        sage: E.prove_BSD(verbosity=2)
        p = 2: True by 2-descent
        True for p not in {2, 3, 5} by Kolyvagin.
        Kolyvagin's bound for p = 3 applies by Lawson-Wuthrich
        Kolyvagin's bound for p = 5 applies by Lawson-Wuthrich
        True for p = 3 by Kolyvagin bound
        True for p = 5 by Kolyvagin bound
        []
        sage: E.prove_BSD(two_desc='pari')
        []

    A rank two curve::

        sage: E = EllipticCurve('389a')

    We know nothing with proof=True::

        sage: E.prove_BSD()
        Set of all prime numbers: 2, 3, 5, 7, ...

    We (think we) know everything with proof=False::

        sage: E.prove_BSD(proof=False)
        []

    A curve of rank 0 and prime conductor::

        sage: E = EllipticCurve('19a')
        sage: E.prove_BSD(verbosity=2)
        p = 2: True by 2-descent
        True for p not in {2, 3} by Kolyvagin.
        Kolyvagin's bound for p = 3 applies by Lawson-Wuthrich
        True for p = 3 by Kolyvagin bound
        []

        sage: E = EllipticCurve('37a')
        sage: E.rank()
        1
        sage: E._EllipticCurve_rational_field__rank
        (1, True)
        sage: E.analytic_rank = lambda : 0
        sage: E.prove_BSD()
        Traceback (most recent call last):
        ...
        RuntimeError: It seems that the rank conjecture does not hold for this curve
        (Elliptic Curve defined by y^2 + y = x^3 - x over Rational Field)!
        This may be a counterexample to BSD, but is more likely a bug.

    We test the consistency check for the 2-part of Sha::

        sage: E = EllipticCurve('37a')
        sage: S = E.sha(); S
        Tate-Shafarevich group for the Elliptic Curve defined by y^2 + y = x^3 - x
         over Rational Field
        sage: def foo(use_database):
        ....:  return 4
        sage: S.an = foo
        sage: E.prove_BSD()
        Traceback (most recent call last):
        ...
        RuntimeError: Apparent contradiction: 0 <= rank(sha[2]) <= 0, but ord_2(sha_an) = 2

    An example with a Tamagawa number at 5::

        sage: E = EllipticCurve('123a1')
        sage: E.prove_BSD(verbosity=2)
        p = 2: True by 2-descent
        True for p not in {2, 5} by Kolyvagin.
        Kolyvagin's bound for p = 5 applies by Lawson-Wuthrich
        True for p = 5 by Kolyvagin bound
        []

    A curve for which 3 divides the order of the Tate-Shafarevich group::

        sage: E = EllipticCurve('681b')
        sage: E.prove_BSD(verbosity=2)               # long time
        p = 2: True by 2-descent...
        True for p not in {2, 3} by Kolyvagin....
        Remaining primes:
        p = 3: irreducible, surjective, non-split multiplicative
            (0 <= ord_p <= 2)
            ord_p(#Sha_an) = 2
        [3]

    A curve for which we need to use ``heegner_index_bound``::

        sage: E = EllipticCurve('198b')
        sage: E.prove_BSD(verbosity=1, secs_hi=1)
        p = 2: True by 2-descent
        True for p not in {2, 3} by Kolyvagin.
        [3]

    The ``return_BSD`` option gives an object with detailed information
    about the proof::

        sage: E = EllipticCurve('26b')
        sage: B = E.prove_BSD(return_BSD=True)
        sage: B.two_tor_rk
        0
        sage: B.N
        26
        sage: B.gens
        []
        sage: B.primes
        []
        sage: B.heegner_indexes
        {-23: 2}

    TESTS:

    This was fixed by :issue:`8184` and :issue:`7575`::

        sage: EllipticCurve('438e1').prove_BSD(verbosity=1)
        p = 2: True by 2-descent...
        True for p not in {2} by Kolyvagin.
        []

    ::

        sage: E = EllipticCurve('960d1')
        sage: E.prove_BSD(verbosity=1)  # long time (4s on sage.math, 2011)
        p = 2: True by 2-descent
        True for p not in {2} by Kolyvagin.
        []

    ::

        sage: E = EllipticCurve('66b3')
        sage: E.prove_BSD(two_desc="pari",verbosity=1)
        p = 2: True by 2-descent
        True for p not in {2} by Kolyvagin.
        []
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
        # Kato's theorem 14.5 requires p>2, potentially good reduction and
        # surjectivity of the representation on E[p]
        primes_to_test = Set(E2.galois_representation().not_surjective())
        primes_to_test += Set(E.sha().an().prime_divisors())
        primes_to_test += Set(E.j_invariant().denominator().prime_divisors())
        primes_to_test = primes_to_test.difference(Set([2]))
    else: # an == 1
        raise NotImplementedError("")
    
    if verbosity > 1:
        print(f"Primes left to test: {primes_to_test}")

    return res


if __name__ == "__main__":
    for la in ['11a', '14a', '20a1', '50b1', '389a',
               '19a', '37a', '123a1', '681b', '198b',
               '26b', '438e1', '960d1', '66b3']:
        E = EllipticCurve(la)
        print(f"Curve: {E.label()} \n old prove_BSD :: {E.prove_BSD()} \n")
        if E.analytic_rank() < 2:
              print(f"{_new_prove_bsd_2(E, E.analytic_rank(), verbosity=2)}\n")
    print("Done.")