# -*- coding: utf-8 -*-
from random import randrange

class AbstractRule:

    def _set_grammar(self, gram):
        self._grammar = gram

    def _calc_valuation(self):
        return None

    def random(self, weight):
        r = randrange(self.count(weight))
        #print("r = ", r, ", count = ", self.count(weight))
        return self.unrank(weight, r)

class ConstantRule(AbstractRule):

    def unrank(self, weight, r):
        if r != 0 :
            raise ValueError("rank not null")
        elif weight != self.valuation():
            raise ValueError("rank greater than count()", weight, self.valuation())
        return self._object
    
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

    def valuation(self):
        return self._valuation

    def _update_valuation(self, val):
        self._valuation = val

class UnionRule(ConstructorRule):

    def __init__(self, fst, snd, org):
        self._fst = fst
        self._snd = snd
        self._valuation = float("inf")
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
        return self.fst().count(weight) + self.snd().count(weight)

    def list(self, weight):
        return self.fst().list(weight) + self.snd().list(weight)

    def unrank(self, weight, rank):
        if rank < 0 or rank >= self.count(weight):
            raise ValueError("rank out of bounds")
        elif rank < self.fst().count(weight):
            return self.fst().unrank(weight, rank)
        else:
            return self.snd().unrank(weight, rank - self.fst().count(weight))
    
    def weight(self, obj):
        if self._origin(obj):
            return self.fst().weight(obj)
        else:
            return self.snd().weight(obj)

class ProductRule(ConstructorRule):

    def __init__(self, fst, snd, cons, dec):
        self._fst = fst
        self._snd = snd
        self._constructor = cons
        self._valuation = float("inf")
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
        s = 0
        for k in range(self.fst().valuation(), weight - self.snd().valuation() + 1):
            s = s + self.fst().count(k) * self.snd().count(weight - k)
        return s

    def list(self, weight):
        ret = []
        for k in range(self.fst().valuation(), weight - self.snd().valuation() + 1):
            for fst_obj in self.fst().list(k):
                for snd_obj in self.snd().list(weight - k):
                    ret = ret + [self._constructor(fst_obj, snd_obj)]
        return ret

    def unrank(self, weight, rank):
        i = 0
        prev_cur_bound = 0
        cur_bound = self.fst().count(i)
        while rank >= cur_bound and i <= weight:
            i = i + 1
            prev_cur_bound = cur_bound # Save value of cur_bound to compute j.
            cur_bound = cur_bound + self.fst().count(i) * self.snd().count(weight - i)
        if rank >= cur_bound:
            raise ValueError("rank out of bounds")
        j = rank - prev_cur_bound
        k = self.fst().count(i)
        return self._constructor(self.fst().unrank(i, j % k), self.snd().unrank(weight - i, int(j / k)))
        
    def weight(self, obj):
        obj1 , obj2 = self._deconstr(obj)
        return self.fst().weight(obj1) + self.snd().weight(obj2) 

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


def vide(obj):
    if obj:
        return False
    else:
        return True

def begins_with(obj, f):
    l = len(f)
    return obj[0:l]==f

def first(obj):
    return obj[0], obj[1:]
    
def last(obj):
    return obj[-1], obj[:-1]

# Grammaire sur les mots de Fibonacci
fiboGram = { "Vide"   : EpsilonRule(""),
             "Fib"    : UnionRule("Vide", "Cas1", vide),
             "Cas1"   : UnionRule("CasAu", "Cas2", lambda x: begins_with(x, 'A')),
             "Cas2"   : UnionRule("AtomB", "CasBAu", lambda x: x=='B'),
             "AtomA"  : SingletonRule("A"),
             "AtomB"  : SingletonRule("B"),
             "CasAu"  : ProductRule("AtomA", "Fib", lambda x, y: x + y, first),
             "CasBAu" : ProductRule("AtomB", "CasAu", lambda x, y: x + y, first)
           }
init_grammar(fiboGram)
print(fiboGram["Fib"].weight("ABABABA"))
#print(calc_valuation(fiboGram))



# Grammaire des mots sur l'alphabet (A,B)
motGram = { "Vide" : EpsilonRule(""),
           "Mot"   : UnionRule("Vide", "Cas1", vide),
           "Cas1"  : UnionRule("Au", "Bu", lambda x: begins_with(x, 'A')),
           "Au"    : ProductRule("AtomA", "Mot", lambda x, y: x + y , first),
           "Bu"    : ProductRule("AtomB", "Mot", lambda x, y:  x + y , first),
           "AtomA" : SingletonRule("A"),
           "AtomB" : SingletonRule("B")
}
init_grammar(motGram)
print(motGram["Mot"].weight("ABABABA"))
#print(calc_valuation(motGram))

def get_rightP(obj):
    lc = 0
    rc = 0
    for i in obj:
        if i=='(':
            lc += 1
        else:
            rc += 1
        if rc > lc:
            return obj[:lc+rc], obj[lc+rc:]
# Grammaire des mots de Dyck
dyckGram = {
    "Vide"  : EpsilonRule(""),
    "Dyck"  : UnionRule("Vide", "(D)D", vide),
    "(D)D"  : ProductRule("Atom(", "D)D", lambda x, y: x + y, first),
    "D)D"   : ProductRule("D)", "Dyck", lambda x, y: x + y, get_rightP),
    "D)"    : ProductRule("Atom)", "Dyck", lambda x, y: y + x, last),
    "Atom(" : SingletonRule("("),
    "Atom)" : SingletonRule(")")
}     

"""
dyckGram = {
    "Vide"  : EpsilonRule(""),
    "Dyck"  : UnionRule("Vide", "Cas1"),
    "Cas1"  : UnionRule("(u)", "uv"),
    "(u)"   : ProductRule("Atom(", "Cas2", lambda x, y: x + y ),
    "Cas2"  : ProductRule("Dyck", "Atom)", lambda x, y: x + y ),
    "Atom(" : SingletonRule("("),
    "Atom)" : SingletonRule(")"),
    "uv"    : ProductRule("Cas1", "Cas1", lambda x, y: x + y ),
}
"""
"""
dyckGram = {
    "Vide"    : EpsilonRule(""),
    "Dyck"    : UnionRule("Vide", "dp-d", vide),
    "dp-d"    : ProductRule("DyckPrm", "Dyck", lambda x, y: x + y ),
    "DyckPrm" : UnionRule("(dp)", "()"),
    "()"      : ProductRule("Atom(", "Atom)", lambda x, y: x + y ),
    "Atom("   : SingletonRule("("),
    "Atom)"   : SingletonRule(")"),
    "(dp)"    : ProductRule("Atom(", "dp)", lambda x, y: x + y ),
    "dp)"     : ProductRule("DyckPrm", "Atom)", lambda x, y: x + y )
}
"""
"""
dyckGram = {
    "Vide"  : EpsilonRule(""),
    "Atom(" : SingletonRule("("),
    "Atom)" : SingletonRule(")"),
    "Dyck" : UnionRule("Vide", "Cas1"),
    "Cas1" : UnionRule("(R", "L)"),
    "(R"   : ProductRule("Atom(", "R", lambda x, y: x + y),
    "R"    : UnionRule("Dyck)", "(RR"),
    "L"    : UnionRule("(Dyck", "LL)"),
    "Dyck)" : ProductRule("Dyck", "Atom)", lambda x, y: x + y),
    "(Dyck" : ProductRule("Atom(", "Dyck", lambda x, y: x + y),
    "L)"   : ProductRule("L", "Atom)", lambda x, y: x + y),
    "(RR" : ProductRule("(R", "R", lambda x, y: x + y),
    "LL)" : ProductRule("L", "L)", lambda x, y: x + y)
}
"""
init_grammar(dyckGram)
print(dyckGram["Dyck"].weight("(()()(()()))"))
print(dyckGram["Dyck"].count(8))
#print(calc_valuation(dyckGram))

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
    "Au"     : ProductRule("AtomA", "restB", lambda x, y: x + y, first),
    "AAu"    : ProductRule("AtomA", "Au", lambda x, y: x + y , first),
    "restB"  : UnionRule("Vide", "CasB", vide),
    "CasB"   : UnionRule("Bu", "BBu", lambda x: unique(x, 'B')),
    "Bu"     : ProductRule("AtomB", "restA", lambda x, y:  x + y , first),
    "BBu"    : ProductRule("AtomB", "Bu", lambda x, y:  x + y , first),
    "restA"  : UnionRule("Vide", "CasA", vide),
    "CasA"   : UnionRule("Au", "AAu", lambda x: unique(x, 'A'))
}

init_grammar(non_tripleGram)
print(non_tripleGram["Non_Triple"].weight("ABABABA"))
#print(calc_valuation(non_tripleGram))



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
    "AuA"    : ProductRule("AtomA", "uA", lambda x, y:  x + y , first),
    "AtomA"  : SingletonRule("A"),
    "uA"     : ProductRule("AtomA", "Pal", lambda x, y:  y + x , last),  # Pour unrank, on a besoin d'avoir une valuation non nulle en 1er
    "BuB"    : ProductRule("AtomB", "uB", lambda x, y:  x + y , first),
    "AtomB"  : SingletonRule("B"),
    "uB"     : ProductRule("AtomB", "Pal", lambda x, y:  y + x , last)
}

init_grammar(palindromeGram)
print(palindromeGram["Pal"].weight("BAB"))
#print(calc_valuation(palindromeGram))

# Grammaire des palindromes sur A, B et C
palindrome2Gram = {
    "Vide"   : EpsilonRule(""),
    "Pal"    : UnionRule("Vide", "Cas1", vide),
    "Cas1"   : UnionRule("AuA", "Cas2", lambda x: XuX(x, 'A')),
    "Cas2"   : UnionRule("BuB", "Cas3", lambda x: XuX(x, 'B')),
    "Cas3"   : UnionRule("CuC", "Cas4", lambda x: XuX(x, 'C')),
    "Cas4"   : UnionRule("AtomA", "Cas5", lambda x: begins_with(x, 'A')),
    "Cas5"   : UnionRule("AtomB", "AtomC", lambda x: begins_with(x, 'B')),
    "AuA"    : ProductRule("AtomA", "uA", lambda x, y: x + y, first ),
    "AtomA"  : SingletonRule("A"),
    "uA"     : ProductRule("AtomA", "Pal", lambda x, y: y + x , last),
    "BuB"    : ProductRule("AtomB", "uB", lambda x, y:  x + y , first),
    "AtomB"  : SingletonRule("B"),
    "uB"     : ProductRule("AtomB", "Pal", lambda x, y:  y + x , last),
    "CuC"    : ProductRule("AtomC", "uC", lambda x, y:  x + y , first),
    "AtomC"  : SingletonRule("C"),
    "uC"     : ProductRule("AtomC", "Pal", lambda x, y:  y + x , last)
}

init_grammar(palindrome2Gram)
#print(calc_valuation(palindrome2Gram))

# Grammaire sur les mots avec autant de lettres de chaque
"""
lettreGram = {
    "Vide"     : EpsilonRule(""),
    "AtomA"    : SingletonRule("A"),
    "AtomB"    : SingletonRule("B"),
    "Lettres"  : UnionRule("Vide", "Cas1"),
    "Cas1"     : UnionRule("ABu", "Cas2"),
    "Cas2"     : UnionRule("BAu", "Cas3"),
    "Cas3"     : UnionRule("AuB", "BuA"),
#    "Cas4"     : UnionRule("BuA", "Cas5"),
#    "Cas5"     : UnionRule("uAB", "uBA"),
    "ABu"      : ProductRule("AtomA", "Bu", lambda x, y: x + y ),
    "Bu"       : ProductRule("AtomB", "Lettres", lambda x, y: x + y),
    "BAu"      : ProductRule("AtomB", "Au", lambda x, y: x + y),
    "Au"       : ProductRule("AtomA", "Lettres", lambda x, y: x + y),
    "AuB"      : ProductRule("Au", "AtomB", lambda x, y: x + y),
    "BuA"      : ProductRule("Bu", "AtomA", lambda x, y: x + y),
#    "uAB"      : ProductRule("uA", "AtomB", lambda x, y: x + y),
    "uA"       : ProductRule("Lettres", "AtomA", lambda x, y: x + y ),
 #   "uBA"      : ProductRule("uB", "AtomA", lambda x, y: x + y ),
    "uB"       : ProductRule("Lettres", "AtomB", lambda x, y: x + y )
}
"""
"""
lettreGram = {
	"Vide"    : EpsilonRule(""),
	"AtomA"   : SingletonRule("A"),
	"AtomB"   : SingletonRule("B"),
	"Lettres" : UnionRule("Vide", "Cas1"),
	"Cas1"    : UnionRule("Ab", "Ba"),
	"Ab"      : ProductRule("AtomA", "b", lambda x, y: x + y ),
	"Ba"      : ProductRule("AtomB", "a", lambda x, y: x + y ),
	"a"       : UnionRule("Au", "Baa"),
	"Au"      : ProductRule("AtomA", "Lettres", lambda x, y: x + y ),
	"Baa"     : ProductRule("Ba", "a", lambda x, y: x + y ),
	"b"       : ProductRule("Bu", "Abb", lambda x, y: x + y ),
	"Bu"      : ProductRule("AtomB", "Lettres", lambda x, y: x + y ),
	"Abb"     : ProductRule("Ab", "b", lambda x, y: x + y )
}

init_grammar(lettreGram)
"""
#print(calc_valuation(lettreGram))

treeGram = {
    "Leaf" : SingletonRule(()),
    "Node" : ProductRule("Tree", "Tree", lambda x, y: (x,y), lambda x: x ),
    "Tree" : UnionRule("Leaf", "Node", lambda x: x==())
}
init_grammar(treeGram)
print(treeGram["Tree"].weight((((),()),())))
"""
print(calc_valuation(treeGram))
print(treeGram["Tree"].count(3))
print(treeGram["Tree"].list(3))
print(treeGram["Tree"].unrank(6,12))
print(treeGram["Tree"].random(3))"""

###########################################
##  Tests sur les grammaires
###########################################
Grams = [(fiboGram,"Fib"), (treeGram,"Tree"), (motGram,"Mot"), \
         (non_tripleGram,"Non_Triple")
         , (dyckGram, "Dyck"), (palindromeGram, "Pal"), (palindrome2Gram, "Pal")]



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
        if i[mainKey].list(4) != [i[mainKey].unrank(4, j) for j in range(i[mainKey].count(4))]:
            return False
    return True


def random_test():
    for (i,mainKey) in Grams:
        l = i[mainKey].list(4)
        for j in range(100):
            if not (i[mainKey].random(4) in l):
                return False
    return True

def all_tests():
    if verif_test():
        print("grammar verification test passed")
    else:
        print("Grammar verification test didn't passed")
    if count_test():
        print("Count and list test passed")
    else:
        print("Count and list test didn't passed")
    if unrank_test():
        print("Unrank test passed")
    else:
        print("Unrank test didn't passed")
    if random_test():
        print("Random test passed")
    else:
        print("Random test didn't pass")

all_tests()