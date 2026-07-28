
from sage.all import *


from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ

def pari_two_descent_work(E) -> tuple:
    r"""
    Prepare the output from pari by two-isogeny.

    INPUT:

    - ``E`` -- an elliptic curve

    OUTPUT: a tuple of 5 elements with the first 4 being integers

    - a lower bound on the rank

    - an upper bound on the rank

    - a lower bound on the rank of Sha[2]

    - an upper bound on the rank of Sha[2]

    - a list of the generators found

    EXAMPLES::

        sage: from sage.schemes.elliptic_curves.BSD import pari_two_descent_work
        sage: E = EllipticCurve('14a')
        sage: pari_two_descent_work(E)
        (0, 0, 0, 0, [])
        sage: E = EllipticCurve('37a')
        sage: pari_two_descent_work(E) # random, up to sign
        (1, 1, 0, 0, [(0 : -1 : 1)])
        sage: E = EllipticCurve('210e7')
        sage: pari_two_descent_work(E)
        (0, 2, 0, 2, [])
        sage: E = EllipticCurve('66b3')
        sage: pari_two_descent_work(E)
        (0, 0, 2, 2, [])
    """
    ep = E.pari_curve()
    lower, rank_upper_bd, s, pts = ep.ellrank()
    gens = sorted([E.point([QQ(x[0]), QQ(x[1])], check=True) for x in pts])
    gens = E.saturation(gens)[0]
    # this is explained in the pari-gp documentation:
    # s is the dimension of Sha[2]/2Sha[4],
    # which is a lower bound for dim Sha[2]
    # dim Sha[2] = dim Sel2 - rank E(Q) - dim tors
    # rank_upper_bd = dim Sel_2 - dim tors - s
    sha_upper_bd = rank_upper_bd - len(gens) + s
    return len(gens), rank_upper_bd, s, sha_upper_bd, gens


def mwrank_two_descent_work(E, two_tor_rk) -> tuple:
    """
    Prepare the output from mwrank two-descent.

    INPUT:

    - ``E`` -- an elliptic curve

    - ``two_tor_rk`` -- its two-torsion rank

    OUTPUT:

    - a lower bound on the rank

    - an upper bound on the rank

    - a lower bound on the rank of Sha[2]

    - an upper bound on the rank of Sha[2]

    - a list of the generators found

    EXAMPLES::

        sage: from sage.schemes.elliptic_curves.BSD import mwrank_two_descent_work
        sage: E = EllipticCurve('14a')
        sage: mwrank_two_descent_work(E, E.two_torsion_rank())
        (0, 0, 0, 0, [])
        sage: E = EllipticCurve('37a')
        sage: mwrank_two_descent_work(E, E.two_torsion_rank())
        (1, 1, 0, 0, [(0 : -1 : 1)])
    """
    MWRC = E.mwrank_curve()
    rank_upper_bd = MWRC.rank_bound()
    rank_lower_bd = MWRC.rank()
    gens = [E(P) for P in MWRC.gens()]
    sha2_lower_bd = MWRC.selmer_rank() - two_tor_rk - rank_upper_bd
    sha2_upper_bd = MWRC.selmer_rank() - two_tor_rk - rank_lower_bd
    return rank_lower_bd, rank_upper_bd, sha2_lower_bd, sha2_upper_bd, gens


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


def new_prove_BSD(E,
                  verbosity=0,
                  two_desc='mwrank',
                  proof=None):
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

    - ``two_desc`` -- string (default: ``'mwrank'``); what to use for the
      two-descent. Options are ``'mwrank' or 'pari'

    - ``proof`` -- boolean or ``None`` (default: None, see
      proof.elliptic_curve or sage.structure.proof). If ``False``, this
      function just immediately returns the empty list.

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

    # first treat CM curves
    if E.has_cm():
        return True
    # now curve is not cm
    # no hope to prove anything if analytic rank is >1
    an = E.analytic_rank()
    if an > 1:
        from sage.sets.primes import Primes
        return Primes()

if __name__ == "__main__":
    for la in ['11a', '14a', '20a1', '50b1', '389a',
               '19a', '37a', '123a1', '681b', '198b',
               '26b', '438e1', '960d1', '66b3']:
        E = EllipticCurve(la)
        print(f"Curve: {E.label()} \n {E.prove_BSD()} \n")
    print("Done.")