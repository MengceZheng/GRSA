import os
import sys
import time
import logging

from sage.all import *
from sage.crypto.util import *

DEBUG_ROOTS = None
BOUND_CHECK = False
USE_FLATTER = True
ACLOG_CLEAR = True

log_file = 'attack.log'  
if ACLOG_CLEAR and os.path.exists(log_file):  
    os.remove(log_file) 
logger = logging.getLogger(__name__)
logging.basicConfig(filename = log_file, level = logging.DEBUG, format = '%(asctime)s - %(levelname)s - %(message)s')


def create_lattice(pr, shifts, bounds, order="invlex", sort_shifts_reverse=False, sort_monomials_reverse=False):
    """
    Creates a lattice from a list of shift polynomials.
    :param pr: the polynomial ring
    :param shifts: the shifts
    :param bounds: the bounds
    :param order: the order to sort the shifts/monomials by
    :param sort_shifts_reverse: set to true to sort the shifts in reverse order
    :param sort_monomials_reverse: set to true to sort the monomials in reverse order
    :return: a tuple of lattice and list of monomials
    """
    logging.debug(f"Creating a lattice with {len(shifts)} shifts ({order = }, {sort_shifts_reverse = }, {sort_monomials_reverse = })...")
    if pr.ngens() > 1:
        pr_ = pr.change_ring(ZZ, order=order)
        shifts = [pr_(shift) for shift in shifts]

    monomials = set()
    for shift in shifts:
        monomials.update(shift.monomials())

    shifts.sort(reverse=sort_shifts_reverse)
    monomials = sorted(monomials, reverse=sort_monomials_reverse)
    L = matrix(ZZ, len(shifts), len(monomials))
    for row, shift in enumerate(shifts):
        for col, monomial in enumerate(monomials):
            L[row, col] = shift.monomial_coefficient(monomial) * monomial(*bounds)

    monomials = [pr(monomial) for monomial in monomials]
    return L, monomials


def reduce_lattice(L, delta=0.8):
    """
    Reduces a lattice basis using a lattice reduction algorithm (currently LLL).
    :param L: the lattice basis
    :param delta: the delta parameter for LLL (default: 0.8)
    :return: the reduced basis
    """
    # logging.debug(f"Reducing a {L.nrows()} x {L.ncols()} lattice...")
    # return L.LLL(delta)
    start_time = time.perf_counter()
    if USE_FLATTER:
        from subprocess import check_output
        from re import findall
        LL = "[[" + "]\n[".join(" ".join(map(str, row)) for row in L) + "]]"
        ret = check_output(["flatter"], input = LL.encode())
        L_reduced = matrix(L.nrows(), L.ncols(), map(int, findall(rb"-?\d+", ret)))
    else:
        L_reduced = L.LLL(delta)
    end_time = time.perf_counter()
    reduced_time = end_time - start_time
    logging.info(f"Reducing a {L.nrows()} x {L.ncols()} lattice within {reduced_time:.3f} seconds...")
    return L_reduced


def reconstruct_polynomials(B, f, modulus, monomials, bounds, preprocess_polynomial=lambda x: x, divide_gcd=True):
    """
    Reconstructs polynomials from the lattice basis in the monomials.
    :param B: the lattice basis
    :param f: the original polynomial (if set to None, polynomials will not be divided by f if possible)
    :param modulus: the original modulus
    :param monomials: the monomials
    :param bounds: the bounds
    :param preprocess_polynomial: a function which preprocesses a polynomial before it is added to the list (default: identity function)
    :param divide_gcd: if set to True, polynomials will be pairwise divided by their gcd if possible (default: True)
    :return: a list of polynomials
    """
    divide_original = f is not None
    modulus_bound = modulus is not None
    logging.debug(f"Reconstructing polynomials ({divide_original = }, {modulus_bound = }, {divide_gcd = })...")
    polynomials = []
    for row in range(B.nrows()):
        norm_squared = 0
        w = 0
        polynomial = 0
        for col, monomial in enumerate(monomials):
            if B[row, col] == 0:
                continue
            norm_squared += B[row, col] ** 2
            w += 1
            assert B[row, col] % monomial(*bounds) == 0
            polynomial += B[row, col] * monomial // monomial(*bounds)

        # Equivalent to norm >= modulus / sqrt(w)
        # Use BOUND_CHECK = False to achieve a successful attack
        if BOUND_CHECK and modulus_bound and norm_squared * w >= modulus ** 2:
            logging.debug(f"Row {row} is too large, ignoring...")
            continue

        polynomial = preprocess_polynomial(polynomial)

        if divide_original and polynomial % f == 0:
            logging.debug(f"Original polynomial divides reconstructed polynomial at row {row}, dividing...")
            polynomial //= f

        if divide_gcd:
            for i in range(len(polynomials)):
                g = gcd(polynomial, polynomials[i])
                # TODO: why are we only allowed to divide out g if it is constant?
                if g != 1 and g.is_constant():
                    logging.debug(f"Reconstructed polynomial has gcd {g} with polynomial at {i}, dividing...")
                    polynomial //= g
                    polynomials[i] //= g

        if polynomial.is_constant():
            logging.debug(f"Polynomial at row {row} is constant, ignoring...")
            continue

        if DEBUG_ROOTS is not None:
            logging.debug(f"Polynomial at row {row} roots check: {polynomial(*DEBUG_ROOTS)}")

        polynomials.append(polynomial)

    logging.debug(f"Reconstructed {len(polynomials)} polynomials")
    return polynomials


def find_roots_univariate(x, polynomial):
    """
    Returns a generator generating all roots of a univariate polynomial in an unknown.
    :param x: the unknown
    :param polynomial: the polynomial
    :return: a generator generating dicts of (x: root) entries
    """
    if polynomial.is_constant():
        return

    for root in polynomial.roots(multiplicities=False):
        if root != 0:
            yield {x: int(root)}


def find_roots_gcd(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses pairwise gcds to find trivial roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if pr.ngens() != 2:
        return

    logging.debug("Computing pairwise gcds to find trivial roots...")
    x, y = pr.gens()
    for i in range(len(polynomials)):
        for j in range(i):
            g = gcd(polynomials[i], polynomials[j])
            if g.degree() == 1 and g.nvariables() == 2 and g.constant_coefficient() == 0:
                # g = ax + by
                a = int(g.monomial_coefficient(x))
                b = int(g.monomial_coefficient(y))
                yield {x: b, y: a}
                yield {x: -b, y: a}


def find_roots_groebner(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses Groebner bases to find the roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    # We need to change the ring to QQ because groebner_basis is much faster over a field.
    # We also need to change the term order to lexicographic to allow for elimination.
    gens = pr.gens()
    s = Sequence(polynomials, pr.change_ring(QQ, order="lex"))
    while len(s) > 0:
        G = s.groebner_basis()
        logging.debug(f"Sequence length: {len(s)}, Groebner basis length: {len(G)}")
        logging.debug(f"Groebner basis: {G = }")
        # special design for this case
        if len(G) == 1 and len(G[0].monomials()) == 4:
            yield G[0]
            return
        if len(G) == len(gens):
            logging.debug(f"Found Groebner basis with length {len(gens)}, trying to find roots...")
            roots = {}
            for polynomial in G:
                vars = polynomial.variables()
                if len(vars) == 1:
                    for root in find_roots_univariate(vars[0], polynomial.univariate_polynomial()):
                        roots |= root

            if len(roots) == pr.ngens():
                yield roots
                return

            logging.debug(f"System is underdetermined, trying to find constant root...")
            G = Sequence(s, pr.change_ring(ZZ, order="lex")).groebner_basis()
            vars = tuple(map(lambda x: var(x), gens))
            for solution_dict in solve([polynomial(*vars) for polynomial in G], vars, solution_dict=True):
                logging.debug(solution_dict)
                found = False
                roots = {}
                for i, v in enumerate(vars):
                    s = solution_dict[v]
                    if s.is_constant():
                        if not s.is_zero():
                            found = True
                        roots[gens[i]] = int(s) if s.is_integer() else int(s) + 1
                    else:
                        roots[gens[i]] = 0
                if found:
                    yield roots
                    return

            return
        else:
            # Remove last element (the biggest vector) and try again.
            s.pop()


def find_roots_resultants(gens, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Recursively computes resultants to find the roots.
    :param polynomials: the reconstructed polynomials
    :param gens: the unknowns
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if len(polynomials) == 0:
        return

    if len(gens) == 1:
        if polynomials[0].is_univariate():
            yield from find_roots_univariate(gens[0], polynomials[0].univariate_polynomial())
    else:
        resultants = [polynomials[0].resultant(polynomials[i], gens[0]) for i in range(1, len(gens))]
        for roots in find_roots_resultants(gens[1:], resultants):
            for polynomial in polynomials:
                polynomial = polynomial.subs(roots)
                if polynomial.is_univariate():
                    for root in find_roots_univariate(gens[0], polynomial.univariate_polynomial()):
                        # Show a root 
                        logging.debug(f"Now root is {root}")
                        yield roots | root


def find_roots_variety(pr, polynomials):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    Uses the Sage variety (triangular decomposition) method to find the roots.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    # We need to change the ring to QQ because variety requires a field.
    s = Sequence([], pr.change_ring(QQ))
    # We use more polynomials (i.e., poly_number) to find the roots, we can further tweak it
    poly_number = int(len(polynomials) * 0.5)
    for i in range(poly_number):
        s.append(polynomials[i])
    I = s.ideal()
    dim = I.dimension()
    logging.debug(f"{I.groebner_basis() = }")
    logging.debug(f"Sequence length: {len(s)}, Ideal dimension: {dim}")
    if dim == 0:
        logging.debug("Found ideal with dimension 0, computing variety...")
        logging.debug(f"The variety is {I.variety(ring=ZZ)}")
        for roots in I.variety(ring=ZZ):
            yield {k: int(v) for k, v in roots.items()}
        return
    elif dim == 1:
        logging.debug("Found ideal with dimension 1...")
        logging.debug(f"{I.groebner_basis()}")
        yield I.groebner_basis()[0]
        return 


def find_roots(pr, polynomials, method="groebner"):
    """
    Returns a generator generating all roots of a polynomial in some unknowns.
    The method used depends on the method parameter.
    :param pr: the polynomial ring
    :param polynomials: the reconstructed polynomials
    :param method: the method to use, can be "groebner", "resultants", or "variety" (default: "groebner")
    :return: a generator generating dicts of (x0: x0root, x1: x1root, ...) entries
    """
    if pr.ngens() == 1:
        logging.debug("Using univariate polynomial to find roots...")
        for polynomial in polynomials:
            yield from find_roots_univariate(pr.gen(), polynomial)
    else:
        # Always try this method because it can find roots the others can't.
        yield from find_roots_gcd(pr, polynomials)

        if method == "groebner":
            logging.debug("Using Groebner basis method to find roots...")
            yield from find_roots_groebner(pr, polynomials)
        elif method == "resultants":
            logging.debug("Using resultants method to find roots...")
            yield from find_roots_resultants(pr.gens(), polynomials)
        elif method == "variety":
            logging.debug("Using variety method to find roots...")
            yield from find_roots_variety(pr, polynomials)


def trivariate_modular(N, e, c, s, t, X, Y, Z, roots_method="groebner"):
    """
    Computes small modular roots of a modular trivariate polynomial.
    More information: Zheng M., Hu H., Wang Z., "Generalized cryptanalysis of RSA with small public exponent" (Section 3)
    :param e: the public exponent
    :param c: the parameter c due to d and e
    :param s: the parameter s
    :param t: the parameter t
    :param X: an approximate bound on the x root
    :param Y: an approximate bound on the y root
    :param Z: an approximate bound on the z root
    :param roots_method: the method to use to find roots (default: "groebner")
    :return: a generator generating small roots (tuples of x, y, z roots) of the polynomial
    """
    pr = ZZ["x", "y", "z"]
    x, y, z = pr.gens()
    f = e * x + y * (N + 1 + z) - 1
    logging.info(f"Polynomial to be solved: {f = }")
    E = e ** (c + 1)
    logging.info(f"Trying {s = }, {t = }...")
    logging.info("Generating shifts...")
    shifts = []
    for r in range(s + 1):
        for i in range(r + 1):
            for j in range(r + 1 - i):
                k = r - i - j
                logging.debug(f"indices: {i = }, {j = }, {k = }")
                g = x ** i * y ** j * f ** k * E ** (s - k)
                shifts.append(g)
    for j in range(1, t + 1):
        for r in range(s + 1):
            for i in range(r + 1):
                k = r - i
                logging.debug(f"indices: {i = }, {j = }, {k = }")
                h = x ** i * z ** j * f ** k * E ** (s - k)
                shifts.append(h)
    
    monomials = set()
    for shift in shifts:
        # for mono in shift.monomials():
        #     if mono not in monomials: 
        #         monomials.add(mono)
        monomials.add(shift.lm())
    logging.debug(f"The monomials: {monomials}")

    logging.info("Generating the lattice...")
    L, monomials = create_lattice(pr, shifts, [X, Y, Z])
    logging.info("Reducing the lattice...")
    L = reduce_lattice(L)
    # x0 = 
    # y0 = 
    # z0 = 
    # logging.debug(f"Test for original {f(x0, y0, z0) % E = }")
    polynomials = reconstruct_polynomials(L, f, E ** s, monomials, [X, Y, Z])
    # for idx, poly in enumerate(polynomials):
    #     result = "0" if poly(x0, y0, z0) % (E ** s) == 0 else "!@#$%"
    #     logging.debug(f"Test for {idx + 1} reconstructed poly(x0, y0, z0) % (E ** s) = {result}")
    #     result = "0" if poly(x0, y0, z0) == 0 else "!@#$%"
    #     logging.debug(f"Test for {idx + 1} reconstructed poly(x0, y0, z0) = {result} over the integers")
    start_time = time.perf_counter()
    solutions = list(find_roots(pr, polynomials, method = roots_method))
    end_time = time.perf_counter()
    solution_time = end_time - start_time
    logging.debug(f"Finding roots within {solution_time:.3f} seconds...")
    R = PolynomialRing(QQbar, 3, names=['x', 'y', 'z'])
    for xyz in solutions:
        if len(solutions) == 1:
            v = R(xyz * e)
            logging.debug(f"Equation: {v.factor() = }")
            print(f"Equation: {v} = 0")
            if v.constant_coefficient() == -1:
                u = QQ(e ** 2 / (N + 1 - v.coefficient({x: 0, y: 1, z: 0})))
                y_ = u.numerator()
                logging.info(f"Guess: {y_ = }")
                logging.debug(f"New equation: {v.subs(y = -y_) = }")
                for x_ in range(int(X / 4), int(X / 2)):
                    z_ = QQ((e * x_ - 1) / y_ - v.coefficient({x: 0, y: 1, z: 0}))
                    if z_.is_integer():
                        logging.info(f"Possible root: {x_ = }, {z_ = }")
                        p = int((sqrt(z_ ** 2 - 4 * N) - z_) / 2)
                        q = int((-z_ - sqrt(z_ ** 2 - 4 * N)) / 2)
                        if p * q == N:
                            return x_, -y_, z_
    return None


def attack_GRSA_instance(N, e, beta, gamma, s = 4):
    """
    Generalized attack on RSA instance with given parameters
    :param N: The modulus value.
    :param e: The public exponent value.
    :param beta: The guess ratio of the bit length of d to the modulus bit length.
    :param gamma: The ratio of the bit length of $d%e$ to e^c (c = 1).
    :param s: The given parameter for controlling the lattice dimension. (default: 4)
    :return: 1 if attack succeeds else 0
    """
    alpha = float(log(e, N))
    c = floor(beta / alpha)
    logging.info(f"Known parameters: {alpha = }, {beta = }, {gamma = }, {c = }")
    X = int(2 * N ** (alpha * gamma * c))
    Y = int(2 * N ** (alpha + beta - 1))
    Z = int(3 * sqrt(N))
    logging.info(f"Upper bounds: {X = }, {Y = }, {Z = }")
    t = max(int(s * (alpha * c - alpha * gamma * c - beta + 1 / 2)), 0)
    start_time = time.perf_counter()
    solution = trivariate_modular(N, e, c, s, t, X, Y, Z)
    end_time = time.perf_counter()
    test_time = end_time - start_time
    if solution is not None:
        _, _, p_q = solution
        p = int((sqrt(p_q ** 2 - 4 * N) - p_q) / 2)
        q = int((-p_q - sqrt(p_q ** 2 - 4 * N)) / 2)
        if p * q == N:
            logging.info(f"Succeeded!")
            logging.info(f"Found {p = }")
            logging.info(f"Found {q = }")
            print(f"Found primes: {p = }, {q = }")
            return 1, test_time
        else:
            logging.info(f"Failed!")
            return 0, test_time
    else:
        print(f"Sorry, cannot attack this GRSA instance...")
        return 0, test_time


if __name__ == "__main__":

    assert len(sys.argv) == 1, f"Usage: sage -python attack.py"

    print(f"Input given parameters of GRSA attack instance as follows")
    N = int(input("Input N: "))
    e = int(input("Input e: "))
    beta = float(input("Input b: "))
    gamma = float(input("Input g: "))
    s = int(input("Input s: "))

    result, test_time = attack_GRSA_instance(N, e, beta, gamma, s)
    if result:
        print(f"The attack costs {test_time:.3f} seconds...")