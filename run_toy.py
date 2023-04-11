from count_eqs import CountEqs
from find_quad_eqs import FindEqs
from sage.all import *

def count_eqs():
    for n in range(8, 17):
        C = CountEqs(n)
        print('==== n = {} ===='.format(n))
        # ---- Gold ----
        print('| Gold: exp = 2^k + 1')
        for k in range(2, n):
            is_bijective = gcd(n, k) == 1 and gcd((1 << n) - 1, (1 << k) + 1) == 1
            a = ((1 << k) + 1) % ((1 << n) - 1)
            num_quad = C.num_quad(a)
            res = f'| Gold: k = {k}, exp = {a}, num_quad = {num_quad}'
            if not is_bijective:
                res += ' (not permutation)'
            print(res)
        print('|')
        # ---- No quad ----
        print('| w/o quad: exp = 2^(r+1)-5')
        for r in range(4, n-2):
            a = (1 << (r+1)) - 5
            num_quad = C.num_quad(a)
            is_exception = check_wo_quad_exception(n, r)
            res = f'| w/o quad: r = {r}, exp = {a}, num_quad = {num_quad}'
            if is_exception:
                res += ' (exception)'
            print(res)
        print('|')
        # ---- Mersenne ----
        print('| Mersenne: exp = 2^k - 1 for odd k')
        for k in range(3, n - 1, 2):
            a = (1 << k) - 1
            num_quad = C.num_quad(a)
            print(f'| Mersenne: k = {k}, exp = {a}, num_quad = {num_quad}')
        print('|')
        # ---- Inv ----
        inv = (1 << n) - 2
        num_quad = C.num_quad(inv)
        print(f'| Inv : exp = {inv}, num_quad = {num_quad}')
        print('|')

def find_quad_eqs():
    for n in range(8, 17):
        F = FindEqs(n)
        C = CountEqs(n)
        print('==== n = {} ===='.format(n))
        # ---- Gold ----
        print('| Gold: exp = 2^k + 1')
        for k in range(2, n):
            is_bijective = gcd(n, k) == 1 and gcd((1 << n) - 1, (1 << k) + 1) == 1
            a = ((1 << k) + 1) % ((1 << n) - 1)
            quad_eqs = F.find_quad(a)
            num_quad = C.num_quad(a)
            assert num_quad == len(quad_eqs), f'Gold exponent 2^{k} + 1 = {a}: find {len(quad_eqs)} eqs but count {num_quad} eqs'
            res = f'| Gold: k = {k}, exp = {a}, num_quad = {num_quad}'
            if not is_bijective:
                res += ' (not permutation)'
            print(res)
        print('|')
        # ---- No quad ----
        print('| w/o quad: exp = 2^(r+1)-5')
        for r in range(4, n-2):
            a = (1 << (r+1)) - 5
            quad_eqs = F.find_quad(a)
            num_quad = C.num_quad(a)
            assert num_quad == len(quad_eqs), f'w/o quad 2^({r} + 1) - 5): find {len(quad_eqs)} eqs but count {num_quad} eqs'
            is_exception = check_wo_quad_exception(n, r)
            res = f'| w/o quad: r = {r}, exp = {a}, num_quad = {num_quad}'
            if is_exception:
                res += ' (exception)'
            print(res)
        print('|')
        # ---- Mersenne ----
        print('| Mersenne: exp = 2^k - 1 for odd k')
        for k in range(3, n - 1, 2):
            a = (1 << k) - 1
            quad_eqs = F.find_quad(a)
            num_quad = C.num_quad(a)
            assert num_quad == len(quad_eqs), f'Mersenne 2^{k} - 1: find {len(quad_eqs)} eqs but count {num_quad} eqs'
            print(f'| Mersenne: k = {k}, exp = {a}, num_quad = {num_quad}')
        print('|')
        # ---- Inv ----
        inv = (1 << n) - 2
        quad_eqs = F.find_quad(inv)
        num_quad = C.num_quad(inv)
        assert num_quad == len(quad_eqs), f'Inv 2^{n} - 2: find {len(quad_eqs)} eqs but count {num_quad} eqs'
        print(f'| Inv: exp = {inv}, num_quad = {num_quad}')
        print('|')

def check_wo_quad_exception(n, r):
    if n == 8 and r == 5:
        return True
    if n == 9:
        return True
    if n == 10 and r == 5:
        return True
    if n == 12 and (r == 4 or r == 8):
        return True
    return False

if __name__ == '__main__':
    print('======== Counting Equations ========')
    count_eqs()

    print('\n======== Finding Quadratic Equations ========')
    find_quad_eqs()
