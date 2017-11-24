# -*- coding: utf-8 -*-
from random import randrange

class AbstractRule:

    def _set_grammar(self, gram):
        self._grammar = gram

    def _calc_valuation(self):
        return None

    def random(self, weight):
        r = randrange(self.count(weight))
        return self.unrank(weight, r)

class ConstantRule(AbstractRule):

    def unrank(self, weight, r):
        if r != 0 :
            raise ValueError("rank not null")
        elif weight != self.valuation():
            raise ValueError("rank greater than count()", weight, self.valuation())
        return self._object

    def rank(self, obj):
        return 0

class EpsilonRule(ConstantRule):

    def __init__(self, obj):
        self._object = obj

    def valuation(self):
        return 0

    def count(self, weight):
        if weight == 0:
            return 1
        else:
            return 0

    def list(self, weight):
        if weight == 0:
            return [self._object]
        else:
            return []
    
    def weight(self, obj):
        if obj:
            raise ValueError("not an instance of epsilon rule")
        return 0

class SingletonRule(ConstantRule):

    def __init__(self, obj):
        self._object = obj

    def valuation(self):
        return 1

    def count(self, weight):
        if weight == 1:
            return 1
        else:
            return 0

    def list(self, weight):
        if weight == 1:
            return [self._object]
        else:
            return []
    
    def weight(self, obj):
        return 1

class ConstructorRule(AbstractRule):

    def __init__(self):
        self._valuation = float("inf")
        self._dict_count = {}
        self._dict_list = {}
        self._dict_unrank = {}
        self._dict_weight = {}
        self._dict_rank = {}

    def valuation(self):
        return self._valuation

    def _update_valuation(self, val):
        self._valuation = val

class UnionRule(ConstructorRule):

    def __init__(self, fst, snd, org):
        super().__init__()
        self._fst = fst
        self._snd = snd
        self._origin = org

    def fst_name(self):
        return self._fst
    def snd_name(self):
        return self._snd
    def fst(self):
        return self._grammar[self._fst]
    def snd(self):
        return self._grammar[self._snd]

    def _calc_valuation(self):
        self._valuation = min(self.fst().valuation(), self.snd().valuation())

    def count(self, weight):
        if weight not in self._dict_count:
            self._dict_count[weight] = \
                    self.fst().count(weight) + self.snd().count(weight)
        return self._dict_count[weight]

    def list(self, weight):
        if weight not in self._dict_list:
            self._dict_list[weight] = \
                    self.fst().list(weight) + self.snd().list(weight)
        return self._dict_list[weight]

    def unrank(self, weight, rank):
        if (weight,rank) not in self._dict_rank:
            if rank < 0 or rank >= self.count(weight):
                raise ValueError("rank out of bounds")
            elif rank < self.fst().count(weight):
                self._dict_unrank[(weight,rank)] = self.fst().unrank(weight, rank)
            else:
                self._dict_unrank[(weight,rank)] = \
                    self.snd().unrank(weight, rank - self.fst().count(weight))
        return self._dict_unrank[(weight,rank)]

    def weight(self, obj):
        if obj not in self._dict_weight:
            if self._origin(obj):
                self._dict_weight[obj] = self.fst().weight(obj)
            else:
                self._dict_weight[obj] = self.snd().weight(obj)
        return self._dict_weight[obj]

    def rank(self, obj):
        if obj not in self._dict_rank:
            if self._origin(obj):
                self._dict_rank[obj] = self.fst().rank(obj)
            else:
                self._dict_rank[obj] = \
                        self.fst().count(self.weight(obj)) + self.snd().rank(obj)
        return self._dict_rank[obj]

class ProductRule(ConstructorRule):

    def __init__(self, fst, snd, cons, dec):
        super().__init__()
        self._fst = fst
        self._snd = snd
        self._constructor = cons
        self._deconstr = dec

    def fst_name(self):
        return self._fst
    def snd_name(self):
        return self._snd
    def fst(self):
        return self._grammar[self._fst]
    def snd(self):
        return self._grammar[self._snd]

    def _calc_valuation(self):
        self._valuation = self.fst().valuation() + self.snd().valuation()

    def count(self, weight):
        if weight not in self._dict_count:
            s = 0
            for k in range(self.fst().valuation(), weight - self.snd().valuation() + 1):
                s = s + self.fst().count(k) * self.snd().count(weight - k)
            self._dict_count[weight] = s
        return self._dict_count[weight]

    def list(self, weight):
        if weight not in self._dict_list:
            ret = []
            for k in range(self.fst().valuation(), weight-self.snd().valuation() + 1):
                for fst_obj in self.fst().list(k):
                    for snd_obj in self.snd().list(weight - k):
                        ret = ret + [self._constructor(fst_obj, snd_obj)]
            self._dict_list[weight] = ret
        return self._dict_list[weight]

    def unrank(self, weight, rank):
        if (weight,rank) not in self._dict_rank:
            offset = 0
            begin_cur_block = 0 # Smallest rank in current block
            end_cur_block = 0 # Biggest rank in current block, plus one
            size_fst = None
            for i in range(self.fst().valuation(), weight - self.snd().valuation() + 1):
                begin_cur_block = end_cur_block
                end_cur_block = begin_cur_block + \
                        self.fst().count(i) * self.snd().count(weight - i)
                if rank < end_cur_block:
                    size_fst = i
                    break
            if not (rank < end_cur_block):
                raise ValueError("rank greater than number of objects in product")
            size_snd = weight - size_fst
            rel_rank = rank - begin_cur_block
            l = self.snd().count(size_snd) # Size of sub-blocks
            self._dict_unrank[(weight,rank)] = \
                self._constructor( \
                    self.fst().unrank(size_fst, int(rel_rank / l)), \
                    self.snd().unrank(size_snd, rel_rank % l)
                )
        return self._dict_unrank[(weight,rank)]
        
    def weight(self, obj):
        if obj not in self._dict_weight:
            obj1 , obj2 = self._deconstr(obj)
            self._dict_weight[obj] = self.fst().weight(obj1) + self.snd().weight(obj2) 
        return self._dict_weight[obj]

    def rank(self, obj):
        if obj not in self._dict_rank:
            (a,b) = self._deconstr(obj)
            # First, the weight of the first component enables us to calculate the
            # offset of the "block" we are in. We calculate this offset using a
            # loop.
            w = self.weight(obj)
            wa = self.fst().weight(a)
            wb = w - wa
            offset = 0
            for i in range(self.fst().valuation(), wa):
                offset += self.fst().count(i) * self.snd().count(w - i)
            # Then we add the offset for second "level" of blocks...
            offset += self.fst().count(wb) * self.fst().rank(a)
            # Then the last offset.
            offset += self.snd().rank(b)
            self._dict_rank[obj] = offset
        return self._dict_rank[obj]

class BoundRule(AbstractRule):

    def __init__(self, gram, minimum, maximum):
        self._gram = gram
        self._min = minimum
        self._max = maximum

    def gram(self):
        return self._grammar[self._gram]

    def valuation(self):
        return max(self._min, self.gram().valuation())

    def count(self, weight):
        if not (weight >= self._min and weight <= self._max):
            return 0
        return self.gram().count(weight)

    def unrank(self, weight, rank):
        if not (weight >= self._min and weight <= self._max):
            raise ValueError("weight is not within bounds")
        return self.gram().unrank(weight, rank)

    def rank(self, obj):
        return self.gram().rank(obj)

    def list(self, weight):
        if not (weight >= self._min and weight <= self._max):
            return []
        return self.gram().list(weight)

    def weight(self, obj):
        w = self.gram().weight(obj)
        if not (w >= self._min and w <= self._max):
            raise ValueError("weight is not within bounds")
        return w

def calc_valuation(gram):
    previous = {}
    fixpoint = False
    while not fixpoint:
        for rule_name,rule_obj in gram.items():
            previous[rule_name] = rule_obj.valuation()
            rule_obj._calc_valuation()
        # Check if fixpoint
        fixpoint = True
        for rule_name,rule_obj in gram.items():
            if previous[rule_name] != rule_obj.valuation():
                fixpoint = False
                break
    return previous

def init_grammar(gram):
    for _,rule_object in gram.items():
        rule_object._set_grammar(gram)
    # Compute valuations to verify grammars
    if float("inf") in calc_valuation(gram).items():
        raise ValueError("Grammaire invalide")

def verif_grammar(gram):
    for _, rule_object in gram.items():
        if rule_object.__class__.__name__ == "UnionRule" or rule_object.__class__.__name__ == "ProductRule":
            if rule_object.fst_name() not in gram.keys():
                #raise ValueError("Grammaire mal ecrite")
                return False
            if rule_object.snd_name() not in gram.keys():
                #raise ValueError("Grammaire mal ecrite")
                return False
    return True

# checks if obj is empty or not
def vide(obj):
    if obj:
        return False
    else:
        return True

# checks if obj starts with the string f or not
def begins_with(obj, f):
    l = len(f)
    return obj[0:l]==f

def first(obj):
    return obj[0], obj[1:]
    
def last(obj):
    return obj[:-1], obj[-1]

# String concatenation function taking two arguments (unlike "".join, which
# takes a sequence
def conc(s1, s2):
    return s1 + s2

# Grammaire sur les mots de Fibonacci
fiboGram = { "Vide"   : EpsilonRule(""),
             "Fib"    : UnionRule("Vide", "Cas1", vide),
             "Cas1"   : UnionRule("CasAu", "Cas2", lambda x: begins_with(x, 'A')),
             "Cas2"   : UnionRule("AtomB", "CasBAu", lambda x: x=='B'),
             "AtomA"  : SingletonRule("A"),
             "AtomB"  : SingletonRule("B"),
             "CasAu"  : ProductRule("AtomA", "Fib", conc, first),
             "CasBAu" : ProductRule("AtomB", "CasAu", conc, first)
           }
init_grammar(fiboGram)


# Grammaire des mots sur l'alphabet (A,B)
motGram = { "Vide" : EpsilonRule(""),
           "Mot"   : UnionRule("Vide", "Cas1", vide),
           "Cas1"  : UnionRule("Au", "Bu", lambda x: begins_with(x, 'A')),
           "Au"    : ProductRule("AtomA", "Mot", conc , first),
           "Bu"    : ProductRule("AtomB", "Mot", conc , first),
           "AtomA" : SingletonRule("A"),
           "AtomB" : SingletonRule("B")
}
init_grammar(motGram)

def before_rightP(obj):
    lc = 0
    rc = 0
    for i in obj:
        if i=='(':
            lc += 1
        else:
            rc += 1
        if rc == lc:
            return obj[:lc+rc-1], obj[lc+rc-1:]
            
# Grammaire des mots de Dyck
dyckGram = {
    "Vide"  : EpsilonRule(""),
    "Dyck"  : UnionRule("Vide", "(D)D", vide),
    "(D)D"  : ProductRule("(D", ")D", conc, before_rightP),
    "(D"   : ProductRule("Atom(", "Dyck", conc, first),
    ")D"    : ProductRule("Atom)", "Dyck", conc, first),
    "Atom(" : SingletonRule("("),
    "Atom)" : SingletonRule(")")
}     
init_grammar(dyckGram)

def unique(obj, f):
    l = len(obj)
    if obj[0]!= f:
        return False
    else:
        if l>1:
            return obj[1]!=f
        return True
   
# Grammaire des mots qui n'ont pas 3 lettres consécutives
non_tripleGram = {
    "Vide"   : EpsilonRule(""),
    "Non_Triple" : UnionRule("Vide", "Cas1", vide),
    "Cas1"   : UnionRule("CasA", "CasB", lambda x: begins_with(x, 'A')),
    "AtomA"  : SingletonRule("A"),
    "AtomB"  : SingletonRule("B"),
    "Au"     : ProductRule("AtomA", "restB", conc, first),
    "AAu"    : ProductRule("AtomA", "Au", conc , first),
    "restB"  : UnionRule("Vide", "CasB", vide),
    "CasB"   : UnionRule("Bu", "BBu", lambda x: unique(x, 'B')),
    "Bu"     : ProductRule("AtomB", "restA", conc , first),
    "BBu"    : ProductRule("AtomB", "Bu", conc , first),
    "restA"  : UnionRule("Vide", "CasA", vide),
    "CasA"   : UnionRule("Au", "AAu", lambda x: unique(x, 'A'))
}
init_grammar(non_tripleGram)

def XuX(obj, X):
    l = len(obj)
    if l==1:
        return False
    else:
        return obj[0]==X    
        
# Grammaire des palindromes sur A, B
palindromeGram = {
    "Vide"   : EpsilonRule(""),
    "Pal"    : UnionRule("Vide", "Cas1", vide),
    "Cas1"   : UnionRule("AuA", "Cas2", lambda x: XuX(x, 'A')),
    "Cas2"   : UnionRule("BuB", "Cas3", lambda x: XuX(x, 'B')),
    "Cas3"   : UnionRule("AtomA", "AtomB", lambda x: begins_with(x, 'A')),
    "AuA"    : ProductRule("Au", "AtomA", conc , last),
    "AtomA"  : SingletonRule("A"),
    "Au"     : ProductRule("AtomA", "Pal", conc , first),
    "BuB"    : ProductRule("Bu", "AtomB", conc , last),
    "AtomB"  : SingletonRule("B"),
    "Bu"     : ProductRule("AtomB", "Pal", conc , first)
}
init_grammar(palindromeGram)

# Grammaire des palindromes sur A, B et C
palindrome2Gram = {
    "Vide"   : EpsilonRule(""),
    "Pal"    : UnionRule("Vide", "Cas1", vide),
    "Cas1"   : UnionRule("AuA", "Cas2", lambda x: XuX(x, 'A')),
    "Cas2"   : UnionRule("BuB", "Cas3", lambda x: XuX(x, 'B')),
    "Cas3"   : UnionRule("CuC", "Cas4", lambda x: XuX(x, 'C')),
    "Cas4"   : UnionRule("AtomA", "Cas5", lambda x: begins_with(x, 'A')),
    "Cas5"   : UnionRule("AtomB", "AtomC", lambda x: begins_with(x, 'B')),
    "AuA"    : ProductRule("Au", "AtomA", conc, last),
    "AtomA"  : SingletonRule("A"),
    "Au"     : ProductRule("AtomA", "Pal", conc , first),
    "BuB"    : ProductRule("Bu", "AtomB", conc , last),
    "AtomB"  : SingletonRule("B"),
    "Bu"     : ProductRule("AtomB", "Pal", conc , first),
    "CuC"    : ProductRule("Cu", "AtomC", conc , last),
    "AtomC"  : SingletonRule("C"),
    "Cu"     : ProductRule("AtomC", "Pal", conc , first)
}
init_grammar(palindrome2Gram)



def split(obj, f):
    cf=0
    co=0
    for i in obj:
        if i==f:
            cf += 1
        else:
            co += 1
        if cf == co:
            return obj[:cf+co], obj[cf+co:]


# Grammaire sur les mots avec autant de lettres de chaque
lettreGram = {
	"Vide"    : EpsilonRule(""),
	"AtomA"   : SingletonRule("A"),
	"AtomB"   : SingletonRule("B"),
	"Lettres" : UnionRule("Vide", "Cas1", vide),
    "Cas1"    : UnionRule("Ab", "Ba", lambda x: begins_with(x, 'A')),
	"Ab"      : ProductRule("AtomA", "b", conc, first),
	"Ba"      : ProductRule("AtomB", "a", conc, first),
    "a"       : UnionRule("Au", "Baa", lambda x: begins_with(x, 'A')),
	"Au"      : ProductRule("AtomA", "Lettres", conc, first),
	"Baa"     : ProductRule("Ba", "a", conc, lambda x: split(x, 'A')),
    "b"       : UnionRule("Bu", "Abb", lambda x: begins_with(x, 'B')),
	"Bu"      : ProductRule("AtomB", "Lettres", conc , first),
	"Abb"     : ProductRule("Ab", "b", conc, lambda x: split(x, 'B'))
}
init_grammar(lettreGram)

# Grammaire sur les arbres binaires
treeGram = {
    "Leaf" : SingletonRule(()),
    "Node" : ProductRule("Tree", "Tree", lambda x, y: (x,y), lambda x: x ),
    "Tree" : UnionRule("Leaf", "Node", lambda x: x==()),
    "BoundTree" : BoundRule("Tree", 2, 9),
    "Test" : ProductRule("Tree", "BoundTree", lambda x, y: (x,y), lambda x: x)
}
init_grammar(treeGram)


###########################################
##  Tests sur les grammaires
###########################################
Grams = [(fiboGram,"Fib"), (motGram,"Mot"), (non_tripleGram,"Non_Triple") , (palindromeGram, "Pal"), (palindrome2Gram, "Pal"), (dyckGram, "Dyck"), (treeGram,"Tree")]

#vérification des grammaire
def verif_test():
    for (i,_) in Grams:
        if not(verif_grammar(i)):
            return False
    return True

# vérification de count et list
def count_test():
    for (i,mainKey) in Grams:
        for j in range(10):
            if len(i[mainKey].list(j)) != i[mainKey].count(j):
                return False
    return True

# vérification de unrank
def unrank_test():
    for (i,mainKey) in Grams:
        if i[mainKey].list(8) != [i[mainKey].unrank(8, j) for j in range(i[mainKey].count(8))]:
            return False
    return True

def random_test():
    for (i,mainKey) in Grams:
        l = i[mainKey].list(4)
        for j in range(100):
            if not (i[mainKey].random(4) in l):
                return False
    return True

def rank_test():
    for (i, mainKey) in Grams:
        l = i[mainKey].list(8)
        r = [i[mainKey].rank(j) for j in l]
        if r != [k for k in range(len(l))]:
            print(l)
            print(mainKey)
            return False
    return True


def all_tests():
    if verif_test():
        print("grammar verification test passed")
    else:
        print("Grammar verification test didn't pass")
    if count_test():
        print("Count and list test passed")
    else:
        print("Count and list test didn't pass")
    if unrank_test():
        print("Unrank test passed")
    else:
        print("Unrank test didn't pass")
    if random_test():
        print("Random test passed")
    else:
        print("Random test didn't pass")
    if rank_test():
        print("Rank test passed")
    else:
        print("Rank test didn't pass")

all_tests()
