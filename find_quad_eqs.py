from functools import reduce
from coset import *
from sage.all import *

class FindEqs:
    def __init__(self, n):
        """Class to count the number of quadratic equations for power mappings over GF(2^n).
        Component:
            n: bit-size of the field
            cst_mod: modulus of the exponent, 2^n - 1
            k: sage object representing GF(2^n)
            alpha: generator of k
            modulus: polynomial modulus of k
            ring: polynomial ring with respect to the x, y variables
            x_var: x variables
            y_var: y variables
            basis: n dimensional basis [alpha_0, ..., alpha_{n-1}] of GF(2^n) over GF(2)
                   where alpha_i = alpha^{i-1}
            A: n by n matrix containing [[alpha_i^{2^j} for 0 <= j < n] for 0 <= i < n]
               where alpha_i = alpha^{i-1}
            B: the inverse matrix of A of the form
               [[beta_j^{2^i} for 0 <= j < n] for 0 <= i < n]
            dual_basis: [beta_0, ..., beta_{n-1}], dual basis of the basis
            basis_trace: for a divisor l of n, basis_trace[l] = [Tr_l^n (alpha_i) for 0 <= i < n]
            kernel_basis: for a divisor l of n, kernel_basis[l] is an n-l dimensional basis
                          of the kernel of the linear transformation Tr_l^n
            rem_basis: for a divisor l of n, rem_basis[l] is an l dimensional basis
                          of the image of the linear transform Tr_l^n
            m_basis_arr: for n = 2m, an m dimensional basis of the image of Tr_m^n
            m_basis: for n = 2m and b in m_basis_arr, m_basis_arr[b] = alpha_i such that
                     Tr_m^n (alpha_i) = b
            m_kernel_basis: for a divisor l of m, m_kernel_basis[l] is an m-l dimensional basis
                            of the kernel of the linear transform Tr_l^m on the image of Tr_m^n
            m_rem_basis: for a divisor l of m, m_rem_basis[l] is an l dimensional basis
                         of the image of the linear transform Tr_l^m on the image of Tr_m^n
        """
        self.n = n
        self.cst_mod = (1 << n) - 1
        self.k = GF(2**n, 'alpha')
        self.alpha = self.k.gen()
        self.modulus = self.k.modulus()
        self.__init_boolean_ring()
        self.__init_basis()
        self.__init_basis_trace()
        self.__init_kernel_basis()
        if n % 2 == 0:
            self.__init_m_basis()
            self.__init_m_basis_trace()
            self.__init_m_kernel_basis()

    def __init_boolean_ring(self):
        var_names = ''
        for i in range(self.n):
            var_names += 'x_{}, '.format(i)
        for i in range(self.n):
            var_names += 'y_{}, '.format(i)
        var_names = var_names[:-2]
        self.ring = BooleanPolynomialRing(var_names)
        self.x_var = self.ring.gens()[:self.n]
        self.y_var = self.ring.gens()[self.n:]

    def __init_basis(self):
        n = self.n
        self.basis = [self.alpha**i for i in range(n)]
        self.mat = MatrixSpace(self.k, self.n, n)
        entry = [0] * (n * n)
        for i in range(n):
            for j in range(n):
                entry[i * n + j] = self.basis[i]**(1 << j)
        self.A = self.mat(entry)
        Ainv = self.A**(-1)
        self.dual_basis = [Ainv[0][i] for i in range(n)]
        self.B = self.mat([Ainv[i % n][i // n] for i in range(n * n)])

        self.bool_mat = MatrixSpace(GF(2), n, n)
        entry = [0] * (n * n)
        for i in range(n):
            poly = self.coeff_wrt_basis(self.dual_basis[i])
            for j in range(n):
                entry[i * n + j] = poly[j]
        self.beta_wrt_alpha_basis = self.bool_mat(entry)
        self.alpha_wrt_beta_basis = self.beta_wrt_alpha_basis**(-1)

    def __init_basis_trace(self):
        self.basis_trace = {}
        for l in divisors(self.n)[:-1]:
            self.basis_trace[l] = [self.trace_l_n(alpha_i, l) for alpha_i in self.basis]

    def __init_kernel_basis(self):
        self.kernel_basis = {}
        self.rem_basis = {}
        for l in self.basis_trace:
            mat_v = []
            for alpha_i in self.basis_trace[l]:
                mat_v += list(self.coeff_wrt_basis(alpha_i))
            mat_v = self.bool_mat(mat_v)
            kernel_basis = kernel(mat_v).basis_matrix()
            assert kernel_basis.nrows() == self.n - l, "wrong kernel basis dimension"
            self.kernel_basis[l] = kernel_basis

            rem_basis = []
            tmp_basis = kernel_basis
            tmp_rank = self.n - l
            for alpha_i in self.basis:
                tmp = vector(self.coeff_wrt_basis(alpha_i))
                ind_test = tmp_basis.stack(tmp)
                if ind_test.rank() == tmp_rank + 1:
                    tmp_rank += 1
                    rem_basis.append(alpha_i)
                    tmp_basis = ind_test
                    if len(rem_basis) == l:
                        break
            self.rem_basis[l] = rem_basis

    def __init_m_basis(self):
        m = self.n // 2
        self.m_basis = {}
        self.m_basis_arr = []
        V = VectorSpace(GF(2), self.n)
        m_basis_coeff_arr = []
        cnt = 0

        for alpha_i in self.basis:
            tr_alpha_i = self.trace_l_n(alpha_i, m, self.n)
            coeff = self.coeff_wrt_basis(tr_alpha_i)
            if tr_alpha_i != self.k(0):
                if cnt == 0:
                    self.m_basis[tr_alpha_i] = alpha_i
                    self.m_basis_arr.append(tr_alpha_i)
                    m_basis_coeff_arr.append(coeff)
                    cnt += 1
                else:
                    W = V.subspace(m_basis_coeff_arr + [coeff])
                    if W.dimension() == cnt + 1:
                        self.m_basis[tr_alpha_i] = alpha_i
                        self.m_basis_arr.append(tr_alpha_i)
                        m_basis_coeff_arr.append(coeff)
                        cnt += 1
            if cnt == m:
                break

    def __init_m_basis_trace(self):
        m = self.n // 2
        self.m_basis_trace = {}
        for l in divisors(m)[:-1]:
            self.m_basis_trace[l] = [self.trace_l_n(alpha_i, l, m) for alpha_i in self.m_basis]

    def __init_m_kernel_basis(self):
        m = self.n // 2
        self.bool_mat_m = MatrixSpace(GF(2), m, self.n)
        self.m_kernel_basis = {}
        self.m_rem_basis = {}
        for l in self.m_basis_trace:
            mat_v = []
            for alpha_i in self.m_basis_trace[l]:
                mat_v += list(self.coeff_wrt_basis(alpha_i))
            mat_v = self.bool_mat_m(mat_v)
            m_kernel_basis = kernel(mat_v).basis_matrix()
            assert m_kernel_basis.nrows() == m - l, "wrong m kernel basis dimension"
            self.m_kernel_basis[l] = m_kernel_basis

            m_rem_basis = {}
            tmp_basis = m_kernel_basis
            tmp_rank = m - l
            for i in range(m):
                tmp = [0] * m
                tmp[i] = 1
                tmp = vector(tmp)
                ind_test = tmp_basis.stack(tmp)
                if ind_test.rank() == tmp_rank + 1:
                    tmp_rank += 1
                    tr_basis_elem = self.m_basis_arr[i]
                    basis_elem = self.m_basis[tr_basis_elem]
                    m_rem_basis[tr_basis_elem] = basis_elem
                    tmp_basis = ind_test
                    if len(m_rem_basis) == l:
                        break
            self.m_rem_basis[l] = m_rem_basis

    def coeff_wrt_basis(self, x):
        """Return a coefficient of x in GF(2^n) wrt the basis.
        """
        poly = list(x.polynomial())
        poly += [0] * (self.n - len(poly))
        return vector(poly)

    def coeff_wrt_dual_basis(self, x):
        """Return a coefficient of x in GF(2^n) wrt the dual basis.
        """
        return self.alpha_wrt_beta_basis * self.coeff_wrt_basis(x)

    def compute_coset_info(self, exp, type):
        """Generate CstInfo object with given exponent and type.
        """
        return CstInfo(exp, self.n, type)

    def compute_quad_coset_info(self, exp, type, kidx):
        """Generate CstInfoQuad object with given exponent, type and k value.
        """
        return CstInfoQuad(exp, self.n, type, kidx)

    def compute_cubic_coset_info(self, exp, type, k1idx, k2idx):
        """Generate CstInfoCubic object with given exponent, type and k values.
        """
        return CstInfoCubic(exp, self.n, type, k1idx, k2idx)

    def trace_n(self, x, n=None):
        """Return Tr_1^n (x).
        """
        if n is None:
            n = self.n
        res = x
        tmp = x
        for _ in range(1, n):
            tmp **= 2
            res += tmp
        return res

    def trace_l_n(self, x, l, n=None):
        """Return Tr_l^n (x) for l | n.
        """
        if n is None:
            n = self.n
        assert n % l == 0, "trace_l_n: l does not divide n"
        res = x
        tmp = x
        for _ in range(1, n // l):
            tmp **= (2**l)
            res += tmp
        return res

    def find_bi_affine(self, a):
        """Find all biaffine equations of y = x^a.
        """
        n = self.n
        cst_info = []
        cst_info.append(self.compute_coset_info(a, CoeffType.Y))
        for k in range(n):
            cst_info.append(self.compute_quad_coset_info((1 << k) + a, CoeffType.XY, k))
        cst_info = sorted(cst_info, key = lambda cst: cst.leader)

        eqs = []
        for k in range(n + 1):
            if hw(cst_info[k].leader) == 1:
                # Case B1
                if cst_info[k].type == CoeffType.XY:
                    eqs += self.__find_xy_eqs_hw_1(cst_info[k])
                else: # cst_info[k].type == CoeffType.Y
                    eqs += self.__find_y_eqs_hw_1(cst_info[k])
            else:
                if cst_info[k].size < n:
                    # Case B2
                    if cst_info[k].type == CoeffType.XY:
                        eqs += self.__find_xy_eqs_kernel(cst_info[k])
                    else: # cst_info[k].type == CoeffType.Y
                        eqs += self.__find_y_eqs_kernel(cst_info[k])
                if k < n and cst_info[k].leader == cst_info[k+1].leader:
                    # Case B3
                    if cst_info[k].type == CoeffType.XY:
                        if cst_info[k+1].type == CoeffType.XY:
                            eqs += self.__find_xy_xy_vanish_eqs(cst_info[k], cst_info[k+1])
                        else: # cst_info[k+1].type == CoeffType.Y
                            eqs += self.__find_xy_y_vanish_eqs(cst_info[k], cst_info[k+1])
                    else: # cst_info[k].type == CoeffType.Y && cst_info[k+1].type == CoeffType.XY
                        eqs += self.__find_xy_y_vanish_eqs(cst_info[k+1], cst_info[k])
        return eqs

    def find_quad(self, a):
        """Find all quadratic equations of y = x^a.
        """
        if self.n % 2 == 0:
            return self.__find_quad_even(a)
        else:
            return self.__find_quad_odd(a)

    def __find_quad_even(self, a):
        """Find all quadratic equations of y = x^a when n is even.
        """
        n = self.n
        m = n // 2
        cst_info = []
        cst_info.append(self.compute_coset_info(a, CoeffType.Y))
        for k in range(n):
            cst_info.append(self.compute_quad_coset_info((1 << k) + a, CoeffType.XY, k))
        for k in range(1, m):
            cst_info.append(self.compute_quad_coset_info(((1 << k) + 1) * a, CoeffType.YY, k))
        cst_info = sorted(cst_info, key = lambda cst: cst.leader)
        cstm_info = self.compute_coset_info(((1 << m) + 1) * a, CoeffType.YY)

        eqs = []
        for k in range(n + m):
            hw_cst_l = hw(cst_info[k].leader)
            if hw_cst_l == 1:
                prev = len(eqs)
                if cst_info[k].type == CoeffType.XY:
                    # Case Q1: hw(2^k + a) = 1
                    eqs += self.__find_xy_eqs_hw_1(cst_info[k])
                elif cst_info[k].type == CoeffType.Y:
                    # Case Q1: hw(a) = 1
                    eqs += self.__find_y_eqs_hw_1(cst_info[k])
                else: # cst_info[k].type == CoeffType.YY
                    # Case Q1: hw((2^k + 1)a) = 1
                    eqs += self.__find_yy_eqs_hw_1(cst_info[k])
                next = len(eqs)
                assert next - prev == n, 'Q1 for hw 1'
            elif hw_cst_l == 2:
                prev = len(eqs)
                if cst_info[k].type == CoeffType.XY:
                    # Case Q1: hw(2^k + a) = 2
                    eqs += self.__find_xy_eqs_hw_2(cst_info[k])
                elif cst_info[k].type == CoeffType.Y:
                    # Case Q1: hw(a) = 2
                    eqs += self.__find_y_eqs_hw_2(cst_info[k])
                else: # cst_info[k].type == CoeffType.YY
                    # Case Q1: hw((2^k + 1)a) = 2
                    eqs += self.__find_yy_eqs_hw_2(cst_info[k])
                next = len(eqs)
                assert next - prev == n, 'Q1 for hw 2'
            else:
                if cst_info[k].size < n:
                    prev = len(eqs)
                    if cst_info[k].type == CoeffType.XY:
                        # Case Q2: |C_{2^k + a}| < n
                        eqs += self.__find_xy_eqs_kernel(cst_info[k])
                    elif cst_info[k].type == CoeffType.Y:
                        # Case Q2: |C_{a}| < n
                        eqs += self.__find_y_eqs_kernel(cst_info[k])
                    else: # cst_info[k].type == CoeffType.YY
                        # Case Q2: |C_{(2^k + 1)a}| < n
                        eqs += self.__find_yy_eqs_kernel(cst_info[k])
                    next = len(eqs)
                    assert next - prev == n - cst_info[k].size, 'Q2'
                if k < n + m - 1 and cst_info[k].leader == cst_info[k+1].leader:
                    prev = len(eqs)
                    if cst_info[k].type == CoeffType.XY:
                        if cst_info[k+1].type == CoeffType.XY:
                            # Case Q3: 2^k + a and 2^{k+1} + a belong to the same coset
                            eqs += self.__find_xy_xy_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                        elif cst_info[k+1].type == CoeffType.Y:
                            # Case Q3: 2^k + a and a belong to the same coset
                            eqs += self.__find_xy_y_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                        else: # cst_info[k+1].type == CoeffType.YY
                            # Case Q3: 2^k + a and (2^{k+1} + 1)a belong to the same coset
                            eqs += self.__find_xy_yy_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                    elif cst_info[k].type == CoeffType.Y:
                        if cst_info[k+1].type == CoeffType.XY:
                            # Case Q3: a and 2^{k+1} + a belong to the same coset
                            eqs += self.__find_xy_y_vanish_rem_eqs(cst_info[k+1], cst_info[k])
                        else: # cst_info[k+1].type == CoeffType.YY
                            # Case Q3: a and (2^{k+1} + 1)a belong to the same coset
                            eqs += self.__find_yy_y_vanish_rem_eqs(cst_info[k+1], cst_info[k])
                    else: # cst_info[k].type == CoeffType.YY
                        if cst_info[k+1].type == CoeffType.XY:
                            # Case Q3: (2^k + 1)a and 2^{k+1} + a belong to the same coset
                            eqs += self.__find_xy_yy_vanish_rem_eqs(cst_info[k+1], cst_info[k])
                        elif cst_info[k+1].type == CoeffType.Y:
                            # Case Q3: (2^k + 1)a and a belong to the same coset
                            eqs += self.__find_yy_y_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                        else: # cst_info[k+1].type == CoeffType.YY
                            # Case Q3: (2^k + 1)a and (2^{k+1} + 1)a belong to the same coset
                            eqs += self.__find_yy_yy_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                    next = len(eqs)
                    assert next - prev == cst_info[k].size, 'Q3'
        hw_cstm_l = hw(cstm_info.leader)
        assert hw_cstm_l != 1, "hw_cstm_l = 1"
        if hw_cstm_l == 2:
            # Case Q1: hw((2^m + 1)a) = 2
            prev = len(eqs)
            eqs += self.__find_yy_m_eqs_hw_2(cstm_info)
            next = len(eqs)
            assert next - prev == m, 'Q1m'
        else:
            if cstm_info.size < m:
                # Case Q2: |C_{(2^m + 1)a}| < m
                prev = len(eqs)
                eqs += self.__find_yy_m_eqs_kernel(cstm_info)
                next = len(eqs)
                assert next - prev == m - cstm_info.size, 'Q2m'
            for k in range(n + m):
                if cstm_info.leader == cst_info[k].leader:
                    prev = len(eqs)
                    if cst_info[k].type == CoeffType.XY:
                        # Case Q3: 2^k + a and (2^m + 1)a belong to the same coset
                        eqs += self.__find_xy_yy_m_vanish_eqs(cst_info[k], cstm_info)
                    elif cst_info[k].type == CoeffType.Y:
                        # Case Q3: a and (2^m + 1)a belong to the same coset
                        eqs += self.__find_y_yy_m_vanish_eqs(cst_info[k], cstm_info)
                    else: # cst_info[k].type == CoeffType.YY
                        # Case Q3: (2^k + 1)a and (2^m + 1)a belong to the same coset
                        eqs += self.__find_yy_yy_m_vanish_eqs(cst_info[k], cstm_info)
                    next = len(eqs)
                    assert next - prev == cstm_info.size, 'Q3m'
                    break
        return eqs

    def __find_quad_odd(self, a):
        """Find all quadratic equations of y = x^a when n is odd.
        """
        n = self.n
        m = n // 2
        cst_info = []
        cst_info.append(self.compute_coset_info(a, CoeffType.Y))
        for k in range(n):
            cst_info.append(self.compute_quad_coset_info((1 << k) + a, CoeffType.XY, k))
        for k in range(1, m + 1):
            cst_info.append(self.compute_quad_coset_info(((1 << k) + 1) * a, CoeffType.YY, k))
        cst_info = sorted(cst_info, key = lambda cst: cst.leader)

        eqs = []
        for k in range(n + m + 1):
            hw_cst_l = hw(cst_info[k].leader)
            if hw_cst_l == 1:
                prev = len(eqs)
                if cst_info[k].type == CoeffType.XY:
                    # Case Q1: hw(2^k + a) = 1
                    eqs += self.__find_xy_eqs_hw_1(cst_info[k])
                elif cst_info[k].type == CoeffType.Y:
                    # Case Q1: hw(a) = 1
                    eqs += self.__find_y_eqs_hw_1(cst_info[k])
                else: # cst_info[k].type == CoeffType.YY
                    # Case Q1: hw((2^k + 1)a) = 1
                    eqs += self.__find_yy_eqs_hw_1(cst_info[k])
                next = len(eqs)
                assert next - prev == n, 'Q1 for hw 1'
            elif hw_cst_l == 2:
                prev = len(eqs)
                if cst_info[k].type == CoeffType.XY:
                    # Case Q1: hw(2^k + a) = 2
                    eqs += self.__find_xy_eqs_hw_2(cst_info[k])
                elif cst_info[k].type == CoeffType.Y:
                    # Case Q1: hw(a) = 2
                    eqs += self.__find_y_eqs_hw_2(cst_info[k])
                else: # cst_info[k].type == CoeffType.YY
                    # Case Q1: hw((2^k + 1)a) = 2
                    eqs += self.__find_yy_eqs_hw_2(cst_info[k])
                next = len(eqs)
                assert next - prev == n, 'Q1 for hw 2'
            else:
                if cst_info[k].size < n:
                    prev = len(eqs)
                    if cst_info[k].type == CoeffType.XY:
                        # Case Q2: |C_{2^k + a}| < n
                        eqs += self.__find_xy_eqs_kernel(cst_info[k])
                    elif cst_info[k].type == CoeffType.Y:
                        # Case Q2: |C_{a}| < n
                        eqs += self.__find_y_eqs_kernel(cst_info[k])
                    else: # cst_info[k].type == CoeffType.YY
                        # Case Q2: |C_{(2^k + 1)a}| < n
                        eqs += self.__find_yy_eqs_kernel(cst_info[k])
                    next = len(eqs)
                    assert next - prev == n - cst_info[k].size, 'Q2'
                if k < n + m and cst_info[k].leader == cst_info[k+1].leader:
                    prev = len(eqs)
                    if cst_info[k].type == CoeffType.XY:
                        if cst_info[k+1].type == CoeffType.XY:
                            # Case Q3: 2^k + a and 2^{k+1} + a belong to the same coset
                            eqs += self.__find_xy_xy_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                        elif cst_info[k+1].type == CoeffType.Y:
                            # Case Q3: 2^k + a and a belong to the same coset
                            eqs += self.__find_xy_y_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                        else: # cst_info[k+1].type == CoeffType.YY
                            # Case Q3: 2^k + a and (2^{k+1} + 1)a belong to the same coset
                            eqs += self.__find_xy_yy_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                    elif cst_info[k].type == CoeffType.Y:
                        if cst_info[k+1].type == CoeffType.XY:
                            # Case Q3: a and 2^{k+1} + a belong to the same coset
                            eqs += self.__find_xy_y_vanish_rem_eqs(cst_info[k+1], cst_info[k])
                        else: # cst_info[k+1].type == CoeffType.YY
                            # Case Q3: a and (2^{k+1} + 1)a belong to the same coset
                            eqs += self.__find_yy_y_vanish_rem_eqs(cst_info[k+1], cst_info[k])
                    else: # cst_info[k].type == CoeffType.YY
                        if cst_info[k+1].type == CoeffType.XY:
                            # Case Q3: (2^k + 1)a and 2^{k+1} + a belong to the same coset
                            eqs += self.__find_xy_yy_vanish_rem_eqs(cst_info[k+1], cst_info[k])
                        elif cst_info[k+1].type == CoeffType.Y:
                            # Case Q3: (2^k + 1)a and a belong to the same coset
                            eqs += self.__find_yy_y_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                        else: # cst_info[k+1].type == CoeffType.YY
                            # Case Q3: (2^k + 1)a and (2^{k+1} + 1)a belong to the same coset
                            eqs += self.__find_yy_yy_vanish_rem_eqs(cst_info[k], cst_info[k+1])
                    next = len(eqs)
                    assert next - prev == cst_info[k].size, 'Q3'
        return eqs

    def brute_force_check(self, f, a):
        n = self.n
        for x in range(2**n):
            sol = {}
            x_str = bin(x)[2:]
            x_str = '0' * (n - len(x_str)) + x_str
            x_bits = [int(x_str[n - (i + 1)]) for i in range(n)]
            X = reduce(lambda acc, cur: acc * self.alpha + cur, reversed(x_bits), 0)
            Y = X**a
            y_bits = self.coeff_wrt_basis(Y)
            for i in range(n):
                sol['x_{}'.format(i)] = x_bits[i]
                sol['y_{}'.format(i)] = y_bits[i]
            if x == 0:
                res = f.subs(sol)
            elif f.subs(sol) != res:
                return False
        return True


    def __compute_xy_eqs(self, arr_b):
        """
        Compute the Boolean equations of the form sum_{i,j} a_{i,j} x_i y_j = 0
        obtained from sum_{b_k in arr_b} Tr_1^n (b_k x^{2^k} y) = 0.
        """
        n = self.n
        coeff_a = [self.coeff_wrt_dual_basis(x) for x in self.A * vector(arr_b)]
        f = 0
        for i in range(n):
            for j in range(n):
                f += coeff_a[i][j] * self.x_var[i] * self.y_var[j]
        return f

    def __compute_y_eqs(self, c):
        """
        Compute the Boolean equations of the form sum_j v_j y_j = 0
        obtained from Tr_1^n (c y) = 0.
        """
        n = self.n
        coeff_v = self.coeff_wrt_dual_basis(c)
        f = 0
        for i in range(n):
            f += coeff_v[i] * self.y_var[i]
        return f

    def __compute_yy_eqs(self, arr_d):
        """
        Compute the Boolean equations of the form sum_{i,j} e_{i,j} y_i y_j = 0
        obtained from sum_{d_k in arr_d} Tr_1^n (d_k y^{2^k + 1}) = 0.
        """
        n = self.n
        coeff_e = [self.coeff_wrt_dual_basis(x) for x in self.A * vector(arr_d)]
        f = 0
        for i in range(n):
            for j in range(n):
                f += coeff_e[i][j] * self.y_var[i] * self.y_var[j]
        return f

    def __find_xy_eqs_hw_1(self, cst_info):
        """
        Find n quadartic equations obtained from Tr_1^n (b_k x^{2^k + a})
        where hw(2^k + a) = 1.
        """
        n = self.n
        eqs = []
        arr_b = [self.k(0)] * n
        kidx = cst_info.kidx
        for alpha_i in self.basis:
            arr_b[kidx] = alpha_i
            f = self.__compute_xy_eqs(arr_b)
            l = cst_info.compute_left_shift(1)
            coeff_u = self.coeff_wrt_dual_basis(arr_b[kidx]**(1 << l))
            for i in range(n):
                f += coeff_u[i] * self.x_var[i]
            eqs.append(f)
        return eqs

    def __find_y_eqs_hw_1(self, cst_info):
        """
        Find n quadartic equations obtained from Tr_1^n (c x^a)
        where hw(a) = 1.
        """
        n = self.n
        eqs = []
        for alpha_i in self.basis:
            c = alpha_i
            f = self.__compute_y_eqs(c)
            l = cst_info.compute_left_shift(1)
            coeff_u = self.coeff_wrt_dual_basis(c**(2**l))
            for i in range(n):
                f += coeff_u[i] * self.x_var[i]
            eqs.append(f)
        return eqs

    def __find_yy_eqs_hw_1(self, cst_info):
        """
        Find n quadratic equations obtained from Tr_1^n (d_k x^{(2^k + 1)a})
        where hw((2^k + 1)a) = 1.
        """
        n = self.n
        eqs = []
        arr_d = [self.k(0)] * n
        kidx = cst_info.kidx
        for alpha_i in self.basis:
            arr_d[kidx] = alpha_i
            f = self.__compute_yy_eqs(arr_d)
            l = cst_info.compute_left_shift(1)
            coeff_u = self.coeff_wrt_dual_basis(arr_d[kidx]**(1 << l))
            for i in range(n):
                f += coeff_u[i] * self.x_var[i]
            eqs.append(f)
        return eqs

    def __find_xy_eqs_hw_2(self, cst_info):
        """
        Find n quadratic equations obtained from Tr_1^n (b_k x^{2^k + a})
        where hw(2^k + a) = 2.
        """
        n = self.n
        eqs = []
        arr_b = [self.k(0)] * n
        kidx = cst_info.kidx
        exp = cst_info.reduced_exp
        exp_one = index_of_one(exp)
        k1 = exp_one[0]
        k2 = exp_one[1]
        for alpha_i in self.basis:
            arr_b[kidx] = alpha_i
            f = self.__compute_xy_eqs(arr_b)
            for i in range(n):
                coeff_c_ii = arr_b[kidx] * self.basis[i]**exp
                coeff_c_ii = int(self.trace_n(coeff_c_ii))
                f += coeff_c_ii * self.x_var[i]
                for j in range(i+1, n):
                    coeff_c_ij = self.basis[i]**(1 << k1) * self.basis[j]**(1 << k2)
                    coeff_c_ij += self.basis[i]**(1 << k2) * self.basis[j]**(1 << k1)
                    coeff_c_ij *= arr_b[kidx]
                    coeff_c_ij = int(self.trace_n(coeff_c_ij))
                    f += coeff_c_ij * self.x_var[i] * self.x_var[j]
            eqs.append(f)
        return eqs

    def __find_y_eqs_hw_2(self, cst_info):
        """
        Find n quadratic equations obtained from Tr_1^n (c x^a) where hw(a) = 2.
        """
        n = self.n
        eqs = []
        exp = cst_info.reduced_exp
        exp_one = index_of_one(exp)
        k1 = exp_one[0]
        k2 = exp_one[1]
        for alpha_i in self.basis:
            c = alpha_i
            f = self.__compute_y_eqs(c)
            for i in range(n):
                coeff_c_ii = c * self.basis[i]**exp
                coeff_c_ii = int(self.trace_n(coeff_c_ii))
                f += coeff_c_ii * self.x_var[i]
                for j in range(i+1, n):
                    coeff_c_ij = self.basis[i]**(1 << k1) * self.basis[j]**(1 << k2)
                    coeff_c_ij += self.basis[i]**(1 << k2) * self.basis[j]**(1 << k1)
                    coeff_c_ij *= c
                    coeff_c_ij = int(self.trace_n(coeff_c_ij))
                    f += coeff_c_ij * self.x_var[i] * self.x_var[j]
            eqs.append(f)
        return eqs

    def __find_yy_eqs_hw_2(self, cst_info):
        """
        Find n quadratic equations obtained from Tr_1^n (d_k x^{(2^k + 1)a})
        where hw((2^k + 1)a) = 2.
        """
        n = self.n
        eqs = []
        arr_d = [self.k(0)] * n
        kidx = cst_info.kidx
        exp = cst_info.reduced_exp
        exp_one = index_of_one(exp)
        k1 = exp_one[0]
        k2 = exp_one[1]
        for alpha_i in self.basis:
            arr_d[kidx] = alpha_i
            f = self.__compute_yy_eqs(arr_d)
            for i in range(n):
                coeff_c_ii = arr_d[kidx] * self.basis[i]**exp
                coeff_c_ii = int(self.trace_n(coeff_c_ii))
                f += coeff_c_ii * self.x_var[i]
                for j in range(i+1, n):
                    coeff_c_ij = self.basis[i]**(1 << k1) * self.basis[j]**(1 << k2)
                    coeff_c_ij += self.basis[i]**(1 << k2) * self.basis[j]**(1 << k1)
                    coeff_c_ij *= arr_d[kidx]
                    coeff_c_ij = int(self.trace_n(coeff_c_ij))
                    f += coeff_c_ij * self.x_var[i] * self.x_var[j]
            eqs.append(f)
        return eqs

    def __find_yy_m_eqs_hw_2(self, cstm_info):
        """
        Find m quadratic equations obtained from Tr_1^m (d'_m x^{(2^m + 1)a})
        where hw((2^m + 1)a) = 2.
        """
        n = self.n
        m = n // 2
        eqs = []
        arr_d = [self.k(0)] * n
        exp = cstm_info.reduced_exp
        exp_one = index_of_one(exp)
        k1 = exp_one[0]
        k2 = exp_one[1]
        for alpha_i in self.m_basis.values():
            arr_d[m] = alpha_i
            f = self.__compute_yy_eqs(arr_d)
            for i in range(n):
                coeff_c_ii = arr_d[m] * self.basis[i]**exp
                coeff_c_ii = int(self.trace_n(coeff_c_ii))
                f += coeff_c_ii * self.x_var[i]
                for j in range(i+1, n):
                    coeff_c_ij = self.basis[i]**(1 << k1) * self.basis[j]**(1 << k2)
                    coeff_c_ij += self.basis[i]**(1 << k2) * self.basis[j]**(1 << k1)
                    coeff_c_ij *= arr_d[m]
                    coeff_c_ij = int(self.trace_n(coeff_c_ij))
                    f += coeff_c_ij * self.x_var[i] * self.x_var[j]
            eqs.append(f)
        return eqs

    def __find_xy_eqs_kernel(self, cst_info):
        """
        Find n - m1 quadratic equations obtained from Tr_1^n (b_k x^{2^k + a})
        where hw(2^k + a) > 2, b_k in ker(Tr_1^n) and m1 = |C_{2^k + a}|.
        """
        n = self.n
        eqs = []
        kernel_basis = self.kernel_basis[cst_info.size]
        kidx = cst_info.kidx
        arr_b = [self.k(0)] * n
        for row in kernel_basis.rows():
            for i in range(n):
                arr_b[kidx] += row[i] * self.basis[i]
            eqs.append(self.__compute_xy_eqs(arr_b))
        return eqs

    def __find_y_eqs_kernel(self, cst_info):
        """
        Find n - m1 quadratic equations obtained from Tr_1^n (c x^a) where hw(a) > 2,
        c in ker(Tr_1^n) and m1 = |C_a|.
        """
        n = self.n
        eqs = []
        kernel_basis = self.kernel_basis[cst_info.size]
        for row in kernel_basis.rows():
            c = self.k(0)
            for i in range(n):
                c += row[i] * self.basis[i]
            eqs.append(self.__compute_y_eqs(c))
        return eqs

    def __find_yy_eqs_kernel(self, cst_info):
        """
        Find n - m1 quadratic equations obtained from Tr_1^n (d_k x^{(2^k + 1)a})
        where hw((2^k + 1)a) > 2, d_k in ker(Tr_1^n), and m1 = |C_{(2^k + 1)a}|.
        """
        n = self.n
        eqs = []
        kernel_basis = self.kernel_basis[cst_info.size]
        kidx = cst_info.kidx
        arr_d = [self.k(0)] * n
        for row in kernel_basis.rows():
            for i in range(n):
                arr_d[kidx] += row[i] * self.basis[i]
            eqs.append(self.__compute_yy_eqs(arr_d))
        return eqs

    def __find_yy_m_eqs_kernel(self, cstm_info):
        """
        Find n - m2 quadratic equations obtained from Tr_1^m (d'_k x^{(2^m + 1)a}) where
        n = 2m, hw((2^m + 1)a) > 2, d'_k in ker(Tr_1^m) and m2 = |C_{(2^m + 1)a}|.
        """
        n = self.n
        m = n // 2
        eqs = []
        m_kernel_basis = self.m_kernel_basis[cstm_info.size]
        arr_d = [self.k(0)] * n
        for row in m_kernel_basis.rows():
            for i in range(m):
                basis_elem = self.m_basis[self.m_basis_arr[i]]
                arr_d[m] += row[i] * basis_elem
            eqs.append(self.__compute_yy_eqs(arr_d))
        return eqs

    def __find_xy_xy_vanish_eqs(self, cst1_info, cst2_info):
        """
        Find n biaffine equations obtained by vanishing Tr_1^n (b_k1 x^{2^k1 + a})
        and Tr_1^n (b_k2 x^{2^k2 + a}) where cst1_info and cst2_info are cosets of
        2^k1 + a and 2^k2 + a belonging to the same coset of size n, respectively.
        """
        n = self.n
        eqs = []
        l = cst2_info.compute_left_shift(cst1_info.exp)
        kidx1 = cst1_info.kidx
        kidx2 = cst2_info.kidx
        arr_b = [self.k(0)] * n
        for alpha_i in self.basis:
            arr_b[kidx2] = alpha_i
            arr_b[kidx1] = alpha_i**(1 << l)
            eqs.append(self.__compute_xy_eqs(arr_b))
        return eqs

    def __find_xy_y_vanish_eqs(self, cst_xy_info, cst_y_info):
        """
        Find n biaffine equations obtained by vanishing Tr_1^n (b_k x^{2^k + a})
        and Tr_1^n (c x^a) where cst_xy_info and cst_y_info are cosets of
        2^k + a and a belonging to the same coset of size n, respectively.
        """
        n = self.n
        eqs = []
        l = cst_y_info.compute_left_shift(cst_xy_info.exp)
        kidx = cst_xy_info.kidx
        arr_b = [self.k(0)] * n
        for alpha_i in self.basis:
            c = alpha_i
            arr_b[kidx] = alpha_i**(1 << l)
            eqs.append(self.__compute_xy_eqs(arr_b) + self.__compute_y_eqs(c))
        return eqs

    def __find_xy_xy_vanish_rem_eqs(self, cst1_info, cst2_info):
        """
        Find m1 quadratic equations obtained by vanishing Tr_1^n (b_k1 x^{2^k1 + a})
        and Tr_1^n (b_k2 x^{2^k2 + a}) where cst1_info and cst2_info are cosets of
        2^k1 + a and 2^k2 + a belonging to the same coset of size m1, respectively.
        """
        n = self.n
        eqs = []
        u = cst2_info.compute_left_shift(cst1_info.exp)
        kidx1 = cst1_info.kidx
        kidx2 = cst2_info.kidx
        arr_b = [self.k(0)] * n
        m1 = cst1_info.size
        basis = self.basis if m1 == n else self.rem_basis[m1]
        for alpha_i in basis:
            arr_b[kidx2] = alpha_i
            arr_b[kidx1] = alpha_i**(1 << u)
            eqs.append(self.__compute_xy_eqs(arr_b))
        return eqs

    def __find_xy_y_vanish_rem_eqs(self, cst_xy_info, cst_y_info):
        """
        Find m1 quadratic equations obtained by vanishing Tr_1^n (b_k x^{2^k + a})
        and Tr_1^n (c x^a) where cst_xy_info and cst_y_info are cosets of
        2^k + a and a belonging to the same coset of size m1, respectively.
        """
        n = self.n
        eqs = []
        u = cst_y_info.compute_left_shift(cst_xy_info.exp)
        kidx = cst_xy_info.kidx
        arr_b = [self.k(0)] * n
        m1 = cst_xy_info.size
        basis = self.basis if m1 == n else self.rem_basis[m1]
        for alpha_i in basis:
            c = alpha_i
            arr_b[kidx] = alpha_i**(1 << u)
            eqs.append(self.__compute_xy_eqs(arr_b) + self.__compute_y_eqs(c))
        return eqs

    def __find_xy_yy_vanish_rem_eqs(self, cst_xy_info, cst_yy_info):
        """
        Find m1 quadratic equations obtained by vanishing Tr_1^n (b_k x^{2^k + a})
        and Tr_1^n (d_k x^{(2^k + 1)a}) where cst_xy_info and cst_yy_info are cosets of
        2^k + a and (2^k + 1)a belonging to the same coset of size m1, respectively.
        """
        n = self.n
        eqs = []
        u = cst_yy_info.compute_left_shift(cst_xy_info.exp)
        kidx_xy = cst_xy_info.kidx
        kidx_yy = cst_yy_info.kidx
        arr_b = [self.k(0)] * n
        arr_d = [self.k(0)] * n
        m1 = cst_xy_info.size
        basis = self.basis if m1 == n else self.rem_basis[m1]
        for alpha_i in basis:
            arr_d[kidx_yy] = alpha_i
            arr_b[kidx_xy] = alpha_i**(1 << u)
            eqs.append(self.__compute_xy_eqs(arr_b) + self.__compute_yy_eqs(arr_d))
        return eqs

    def __find_yy_y_vanish_rem_eqs(self, cst_yy_info, cst_y_info):
        """
        Find m1 quadratic equations obtained by vanishing Tr_1^n (d_k x^{(2^k + 1)a})
        and Tr_1^n (c x^a) where cst_yy_info and cst_y_info are cosets of (2^k + 1)a and a
        belonging to the same coset of size m1, respectively.
        """
        n = self.n
        eqs = []
        u = cst_y_info.compute_left_shift(cst_yy_info.exp)
        kidx = cst_yy_info.kidx
        arr_d = [self.k(0)] * n
        m1 = cst_yy_info.size
        basis = self.basis if m1 == n else self.rem_basis[m1]
        for alpha_i in basis:
            c = alpha_i
            arr_d[kidx] = alpha_i**(1 << u)
            eqs.append(self.__compute_yy_eqs(arr_d) + self.__compute_y_eqs(c))
        return eqs

    def __find_yy_yy_vanish_rem_eqs(self, cst1_info, cst2_info):
        """
        Find m1 quadratic equations obtained by vaninshing Tr_1^n (d_k1 x^{(2^k1 + 1)a})
        and Tr_1^n (d_k2 x^{(2^k2 + 1)a}) where cst1_info and cst2_info are cosets of
        (2^k1 + 1)a and (2^k2 + 1)a belonging to the same coset of size m1, respectively.
        """
        n = self.n
        eqs = []
        u = cst2_info.compute_left_shift(cst1_info.exp)
        kidx1 = cst1_info.kidx
        kidx2 = cst2_info.kidx
        arr_d = [self.k(0)] * n
        m1 = cst1_info.size
        basis = self.basis if m1 == n else self.rem_basis[m1]
        for alpha_i in basis:
            arr_d[kidx2] = alpha_i
            arr_d[kidx1] = alpha_i**(1 << u)
            eqs.append(self.__compute_yy_eqs(arr_d))
        return eqs

    def __find_xy_yy_m_vanish_eqs(self, cst_xy_info, cstm_info):
        """
        Find m2 quadratic equations obtained by vanishing Tr_1^n (b_k x^{2^k + a})
        and Tr_1^m (d'_m x^{(2^m + 1)a}) where cst_xy_info and cstm_info are cosets of
        2^k + a and (2^m + 1)a belonging to the same coset of m2, respectively.
        """
        n = self.n
        m = n // 2
        eqs = []
        u = cstm_info.compute_left_shift(cst_xy_info.exp)
        kidx = cst_xy_info.kidx
        arr_b = [self.k(0)] * n
        arr_d = [self.k(0)] * n
        m2 = cstm_info.size
        basis = self.m_basis if m2 == m else self.m_rem_basis[m2]
        for basis_elem in basis.values():
            arr_d[m] = basis_elem
            arr_b[kidx] = basis_elem**(1 << u)
            eqs.append(self.__compute_xy_eqs(arr_b) + self.__compute_yy_eqs(arr_d))
        return eqs

    def __find_y_yy_m_vanish_eqs(self, cst_y_info, cstm_info):
        """
        Find m2 quadratic equations obtained by vanishing Tr_1^n (c x^a) and
        Tr_1^m (d'_m x^{(2^m + 1)a}) where cst_y_info and cstm_info are cosets of
        a and (2^m + 1)a belonging to the same coset of size m2, respectively.
        """
        n = self.n
        m = n // 2
        eqs = []
        u = cstm_info.compute_left_shift(cst_y_info.exp)
        arr_d = [self.k(0)] * n
        m2 = cstm_info.size
        basis = self.m_basis if m2 == m else self.m_rem_basis[m2]
        for basis_elem in basis.values():
            arr_d[m] = basis_elem
            c = basis_elem**(1 << u)
            eqs.append(self.__compute_yy_eqs(arr_d) + self.__compute_y_eqs(c))
        return eqs

    def __find_yy_yy_m_vanish_eqs(self, cst_yy_info, cstm_info):
        """
        Find m2 quadratic equations obtained by vanishing Tr_1^n (d_k x^{(2^k + 1)a})
        and Tr_1^m (d'_m x^{(2^m + 1)a}) where cst_yy_info and cstm_info are cosets of
        (2^k + 1)a and (2^m + 1)a belonging to the same coset of size m2, respectively.
        """
        n = self.n
        m = n // 2
        eqs = []
        u = cstm_info.compute_left_shift(cst_yy_info.exp)
        kidx = cst_yy_info.kidx
        arr_d = [self.k(0)] * n
        m2 = cstm_info.size
        basis = self.m_basis if m2 == m else self.m_rem_basis[m2]
        for basis_elem in basis.values():
            arr_d[m] = basis_elem
            arr_d[kidx] = basis_elem**(1 << u)
            eqs.append(self.__compute_yy_eqs(arr_d))
        return eqs
