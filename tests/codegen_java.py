
import io
import unittest

from cozy.target_syntax import *
from cozy.codegen import JavaPrinter

def mk_lambda(n, t, l):
    v = EVar(n).with_type(t)
    return ELambda(v, l(v))

class TestCodegen(unittest.TestCase):
    def test_construct_concrete_list(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)
            
            bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda("x", INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
            
            out = codgen.render_expr(bag, {})
            self.assertEqual(out.setup, "\n".join([
                "Bag<Integer> filtered1 = new Bag<Integer>();",
                "for (Integer item2 : v) {",
                "    if ((item2 > 0)) {",
                "        filtered1.add(item2);",
                "    }",
                "}",
            ]))
            self.assertEqual(out.inline, "filtered1")

    def test_construct_concrete_map(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)
            
            bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda("x", INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
            map = EMakeMap2(bag, mk_lambda("x", INT, lambda k: k)).with_type(TMap(INT, INT))
            
            out = codgen.render_expr(map, {})

            self.assertEqual(out.setup, "\n".join([
                "Bag<Integer> filtered2 = new Bag<Integer>();",
                "for (Integer item3 : v) {",
                "    if ((item3 > 0)) {",
                "        filtered2.add(item3);",
                "    }",
                "}",
                "java.util.HashMap<Integer, Integer> make1 = new java.util.HashMap<Integer, Integer>();",
                "for (Integer key4 : filtered2) {",
                "    make1.set(key4, key4);",
                "}",
            ]))
            self.assertEqual(out.inline, "make1")

    def test_distinct_foreach(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)

            bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda("x", INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
            x = EVar("x").with_type(INT)
            v = EVar("v").with_type(INT)
            stm = SForEach(x, EUnaryOp(UOp.Distinct, bag).with_type(TSet(INT)), SAssign(v, x))
            out = codgen.render_stmt(stm)

            self.assertEqual(out, "\n".join([
                "Bag<Integer> filtered1 = new Bag<Integer>();",
                "for (Integer item2 : v) {",
                "    if ((item2 > 0)) {",
                "        filtered1.add(item2);",
                "    }",
                "}",
                "for (Integer x : filtered1.distinct()) {",
                "    v = x;",
                "}",
            ]))

    def test_distinct(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)
            
            bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda("x", INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))
            
            out = codgen.render_expr(EUnaryOp(UOp.Distinct, bag).with_type(TSet(INT)), {})

            self.assertEqual(out.setup, "\n".join([
                "Bag<Integer> filtered1 = new Bag<Integer>();",
                "for (Integer item2 : v) {",
                "    if ((item2 > 0)) {",
                "        filtered1.add(item2);",
                "    }",
                "}",
            ]))
            self.assertEqual(out.inline, "filtered1.distinct()")

    def test_len(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)

            bag = EFilter(EVar("v").with_type(TBag(INT)), mk_lambda("x", INT, lambda x: EBinOp(x, ">", ZERO))).with_type(TBag(INT))

            out = codgen.render_expr(EUnaryOp(UOp.Length, bag).with_type(TSet(INT)), {})
            
            self.assertEqual(out.setup, "\n".join([
                "Bag<Integer> filtered1 = new Bag<Integer>();",
                "for (Integer item2 : v) {",
                "    if ((item2 > 0)) {",
                "        filtered1.add(item2);",
                "    }",
                "}",
            ]))
            self.assertEqual(out.inline, "filtered1.size()")

    def test_all(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)

            bag = EVar("somebag").with_type(TBag(BOOL))

            out = codgen.render_expr(EUnaryOp(UOp.All, bag).with_type(BOOL), {})
            
            self.assertEqual(out.setup, "\n".join([
                "Boolean all1 = true;",
                "for (Boolean term2 : somebag){",
                "    all1 = all1 && term2;",
                "}",
            ]))
            self.assertEqual(out.inline, "all1")
    
    def test_any(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)

            bag = EVar("somebag").with_type(TBag(BOOL))

            out = codgen.render_expr(EUnaryOp(UOp.Any, bag).with_type(BOOL), {})
            
            self.assertEqual(out.setup, "\n".join([
                "Boolean any1 = false;",
                "for (Boolean term2 : somebag){",
                "    any1 = any1 || term2;",
                "}",
            ]))
            self.assertEqual(out.inline, "any1")

    def test_argmin(self):
        with io.StringIO() as f:
            codgen = JavaPrinter(out=f)

            bag = EMap(EVar("v").with_type(TBag(INT)), mk_lambda("x", INT, lambda x: EBinOp(x, ">", ZERO).with_type(BOOL))).with_type(TBag(BOOL))

            e = EArgMin(bag, mk_lambda("x", INT, lambda x: EUnaryOp("-", x).with_type(x.type))).with_type(INT)

            out = codgen.render_expr(e, {})
            
            self.assertEqual(out.setup, "\n".join([
                "Bag<Boolean> mapped5 = new Bag<Boolean>();",
                "for (Boolean item6 : v) {",
                "    mapped5.add((item6 > 0));",
                "}",
                "Integer argmin1 = null;",
                "Integer score2 = null;",
                "for (Integer candidate3 : mapped5) {",
                "    Integer candidate_score4 = (-candidate3);",
                "    if (argmin1 == null || candidate_score4 < score2) {",
                "        argmin1 = candidate3;",
                "        score2 = candidate_score4;",
                "    }",
                "}",
            ]))
            self.assertEqual(out.inline, "argmin1")