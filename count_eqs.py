from functools import reduce
from coset import *
from sage.all import *

class CountEqs:
    """Class to count the number of quadratic equations for power mappings over GF(2^n).
    Component:
        n: bit-size of the field
        cst_mod: modulus of the exponent, 2^n - 1
        k: sage object representing GF(2^n)
        alpha: generator of k
        modulus: polynomial modulus of k
    """
    def __init__(self, n):
        self.n = n
        self.cst_mod = (1 << n) - 1

        self.k = GF(2**n, 'alpha')
        self.alpha = self.k.gen()
        self.modulus = self.k.modulus()

    def compute_coset_info(self, exp, type):
        """Generate CstInfo object with given exponent and type.
        """
        return CstInfo(exp, self.n, type)

    def compute_quad_coset_info(self, exp, type, kidx):
        """Generate CstInfoQuad object with given exponent, type and k value.
        """
        return CstInfoQuad(exp, self.n, type, kidx)

    def num_bi_affine(self, a):
        """Count the number of biaffine equations of y = x^a
        """
        n = self.n
        # h(x, y) = Tr_1^n (c y) + sum_{k=0}^{n-1} Tr_1^n (b_k x^{2^k} y)

        ind_cst_info = []
        # Tr_1^n (c y) = Tr_1^n (c x^a)
        ind_cst_info.append(self.compute_coset_info(a, CoeffType.Y))
        for k in range(n):
            # Tr_1^n (b_k x^{2^k} y) = Tr_1^n (b_k x^{2^k + a})
            ind_cst_info.append(self.compute_coset_info((1 << k) + a, CoeffType.XY))
        ind_cst_info = sorted(ind_cst_info, key = lambda cst: cst.leader)

        eqn = 0
        num_case_3 = 0
        for i in range(n+1):
            if hw(ind_cst_info[i].leader) == 1:
                eqn += n
            else:
                if ind_cst_info[i].size < n:
                    eqn += n - ind_cst_info[i].size
                if i < n and ind_cst_info[i].leader == ind_cst_info[i+1].leader:
                    num_case_3 += 1
                elif num_case_3 > 0:
                    eqn += ind_cst_info[i-1].size * num_case_3
                    num_case_3 = 0
        return eqn

    def num_quad(self, a):
        """Count the number of quadratic equations of y = x^a
        """
        n = self.n
        m = n // 2
        # h(x, y) = Tr_1^n (c y) + sum_{k=0}^{n-1} Tr_1^n (b_k x^{2^k} y)
        #           + sum_{k=0}^{n} Tr_1^n (d_k y^{2^k + 1})
        #         = Tr_1^n (c' y) + sum_{k=0}^{n-1} Tr_1^n (b_k x^{2^k} y)
        #           + sum_{k=1}^{m-1} Tr_1^n (d'_k y^{2^k + 1}) + Tr_1^n (d_m y^{2^m + 1})
        # where
        #     * Tr_1^n (c y) + Tr_1^n (d_0 y^2) = Tr_1^n (c' y) for c' = c + d_0^{2^{n-1}}.
        #     * Tr_1^n (d_k y^{2^k + 1}) + Tr_1^n (d_{n-k} y^{2^{n-k} + 1}) = Tr_1^n (d'_k y^{2^k + 1})
        #       for 1 <= k < m and d'_k = d_k + d_{n-k}^{2^k}.
        #     * When n = 2m, Tr_1^n (d_m y^{2^m + 1}) = Tr_1^m (d'_m y^{2^m + 1})
        #       for d'_m = Tr_m^n (d_m).

        ind_cst_info = []
        # Tr_1^n (c' y) = Tr_1^n (c' x^a)
        ind_cst_info.append(self.compute_coset_info(a, CoeffType.Y))
        for k in range(n):
            # Tr_1^n (b_k x^{2^k} y) = Tr_1^n (b_k x^{2^k + a})
            ind_cst_info.append(self.compute_quad_coset_info((1 << k) + a, CoeffType.XY, k))
        for k in range(1, m + 1):
            # Tr_1^n (d'_k y^{2^k + 1}) = Tr_1^n (d'_k x^{(2^k + 1)a})
            ind_cst_info.append(self.compute_quad_coset_info(((1 << k) + 1) * a, CoeffType.YY, k))
        ind_cst_info = sorted(ind_cst_info, key = lambda x: x.leader)
        num_ind_cst = len(ind_cst_info)

        eqn = 0
        num_case_3 = 0
        for i in range(num_ind_cst):
            hw_cst_l = hw(ind_cst_info[i].leader)
            if hw_cst_l == 1 or hw_cst_l == 2:
                eqn += ind_cst_info[i].pair_cst.size
            else:
                if ind_cst_info[i].size < ind_cst_info[i].pair_cst.size:
                    eqn += ind_cst_info[i].pair_cst.size - ind_cst_info[i].size
                if i < num_ind_cst - 1 and ind_cst_info[i].leader == ind_cst_info[i+1].leader:
                    num_case_3 += 1
                elif num_case_3 > 0:
                    eqn += ind_cst_info[i-1].size * num_case_3
                    num_case_3 = 0
        return eqn
