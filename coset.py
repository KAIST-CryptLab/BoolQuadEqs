from enum import Enum

def hw(x):
    """
    Compute hamming weight of x
    """
    w = 0
    while x:
        w += x % 2
        x //= 2
    return w

def index_of_one(x):
    index = []
    i = 0
    while x:
        if x % 2 == 1:
            index.append(i)
        x //= 2
        i += 1
    return index

class CoeffType(Enum):
    """
    Enum class denoting the type of variable
        Y: y_i for some i
        XY: x_i y_j for some i, j
        YY: y_i y_j for some i != j
    """
    Y = 1
    XY = 2
    YY = 3

class CstInfo:
    """
    Class denoting the coset of exp mod 2^n - 1,
    i.e., terms in Tr(x^exp) for x in GF(2^n).
    Component:
        exp: input exponent
        n: bit-size of the field
        reduced_exp: exp mod 2^n - 1
        cst: set of coset elements
        leader: coset leader
        size: size of the coset
        type: variable type
        pair_cst: pair coset info when variable type is Y
    """
    def __init__(self, exp, n, type):
        self.exp = exp
        self.n = n
        self.mod = (1 << n) - 1
        self.reduced_exp = exp % self.mod
        self.__init_coset()
        self.leader = min(self.cst)
        self.size = len(self.cst)
        self.type = type
        if type == CoeffType.Y:
            self.pair_cst = PairCstInfo(n, 0, 1, is_compute_cst=False)
            self.pair_cst.leader = None
            self.pair_cst.size = n

    def __init_coset(self):
        e = self.exp % self.mod
        self.cst = [e]
        next = (e << 1) % self.mod
        while next not in self.cst:
            self.cst.append(next)
            next = (next << 1) % self.mod

    def print_info(self):
        print('cst info: exp {} of hw {}, type {}, leader {}, size {}'.format(self.reduced_exp, hw(self.reduced_exp), self.type, self.leader, self.size))

    def compute_left_shift(self, des):
        """
        Return idx such that cst_leader << idx == des
               -1 if des is not in the coset
        """
        des = des % self.mod
        return self.cst.index(des)

class PairCstInfo:
    """
    Class denoting the pair coset of (s1, s2) mod 2^n - 1,
    i.e., terms in Tr(x^s1 y^s2) for x in GF(2^n).
    Component:
        s1: input exponent of x variable
        s2: input exponent of y variable
        n: bit-size of the field
        cst: set of all coset elements
        leader: coset leader
        size: size of the coset
    """
    def __init__(self, n, s1, s2, is_compute_cst=True):
        self.n = n
        self.mod = (1 << n) - 1
        self.s1 = s1 % self.mod
        self.s2 = s2 % self.mod
        if is_compute_cst:
            self.__init_coset()
            self.leader = min(self.cst, key = lambda e: e[0] * self.mod + e[1])
            self.size = len(self.cst)

    def __init_coset(self):
        e = (self.s1, self.s2)
        self.cst = [e]
        next = ((e[0] << 1) % self.mod, (e[1] << 1) % self.mod)
        while next not in self.cst:
            self.cst.append(next)
            next = ((next[0] << 1) % self.mod, (next[1] << 1) % self.mod)

class CstInfoQuad(CstInfo):
    """
    Subclass of CstInfo denoting the coset of quadratic variables
    which is either (2^k, 1) or (0, 2^k + 1),
    i.e., terms in Tr(x^{2^k} y) or Tr(y^{2^k + 1}) in GF(2^n)
    Component:
        kidx: value of k
        type: type of variable (either XY or YY)
        pair_cst: pair coset info
    """
    def __init__(self, exp, n, type, kidx):
        """
        Initialize CstInfoQuad object for quadratic monomials
        appearing in y = x^a over GF(2^n)
        Args:
            exp: exponent of the coset
                When type == CoeffType.XY, exp == 2^k + a
                When type == CoeffType.YY, exp == 2^k + 1
            n: bit-size of the field
            type: variable type
            kidx: value of k
        """
        is_valid_type = (type == CoeffType.XY) or (type == CoeffType.YY)
        assert is_valid_type, 'CstInfoQuad: invalid cst type'
        super().__init__(exp, n, type)
        self.kidx = kidx
        if type == CoeffType.XY:
            self.pair_cst = PairCstInfo(n, 1 << kidx, 1, is_compute_cst=False)
            self.pair_cst.leader = None
            self.pair_cst.size = n
        else: # type == CoeffType.YY
            assert kidx != 0, 'CstInfoQuad: YY invalid kidx'
            self.pair_cst = PairCstInfo(n, 0, 1 << kidx + 1, is_compute_cst=False)
            self.pair_cst.leader = None
            self.pair_cst.size = n if n % 2 != 0 or kidx != n // 2 else n // 2

    def print_info(self):
        print('cst info: exp {} of hw {}, type {}, leader {}, size {}, kidx {}'.format(
            self.reduced_exp, hw(self.reduced_exp), self.type, self.leader, self.size, self.kidx
        ))
