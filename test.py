from count_eqs import CountEqs
from find_quad_eqs import FindEqs
from sage.all import *

def test_bi_affine(n, check_all_val=True):
    F = FindEqs(n)
    C = CountEqs(n)
    failed_list = []
    for a in range(2, (1 << n) - 1):
        print('Test for a = {}...'.format(a))
        eqs = F.find_bi_affine(a)
        num = C.num_bi_affine(a)
        if len(eqs) != num:
            print('  Test fails: found {} eqs but there are {} eqs'.format(len(eqs), num))
            failed_list.append(a)
            continue
        if len(eqs) == 0:
            print('  No bi-affine eqs')
            continue
        seq = Sequence(eqs)
        M, _ = seq.coefficient_matrix()
        if len(eqs) != M.rank():
            print('  Test fails: not linearly independent')
            failed_list.append(a)
            continue
        if check_all_val:
            for f in eqs:
                if not F.brute_force_check(f, a):
                    print('  Test fails: not valid equation')
                    print(f)
                    failed_list.append(a)
                    break
        print('  {} bi-affine eqs'.format(len(eqs)))
    if len(failed_list) == 0:
        if check_all_val:
            print('Pass for all a (checked all inputs)')
        else:
            print('Pass for all a (only checked linear independence)')
    else:
        print('Fail for a in', failed_list)
        exit()

def test_quadratic(n, check_all_val=True):
    F = FindEqs(n)
    C = CountEqs(n)
    failed_list = []
    for a in range(2, (1 << n) - 1):
        print('Test for a = {}...'.format(a))
        eqs = F.find_quad(a)
        num = C.num_quad(a)
        if len(eqs) != num:
            print('  Test fails: found {} eqs but there are {} eqs'.format(len(eqs), num))
            failed_list.append(a)
            continue
        if len(eqs) == 0:
            print('  No quadratic eqs')
            continue
        seq = Sequence(eqs)
        M, _ = seq.coefficient_matrix()
        if len(eqs) != M.rank():
            print('  Test fails: not linearly independent')
            failed_list.append(a)
            continue
        if check_all_val:
            for f in eqs:
                if not F.brute_force_check(f, a):
                    print('  Test fails: not valid equation')
                    print(f)
                    failed_list.append(a)
                    break
        print('  {} quadratic eqs'.format(len(eqs)))
    if len(failed_list) == 0:
        if check_all_val:
            print('Pass for all a (checked all inputs)')
        else:
            print('Pass for all a (only checked linear independence)')
    else:
        print('Fail for a in', failed_list)
        exit()

if __name__ == '__main__':
    n = 6
    print('==== Test Biaffine ====')
    test_bi_affine(n)

    print('\n==== Test Quadratic ====')
    test_quadratic(n)
