from contextlib import contextmanager
from collections import OrderedDict
import itertools
import json
from typing import *

import sys

def debug(msg):
    sys.stderr.write(repr(msg) + '\n')

from cozy import common, evaluation
from cozy.target_syntax import *
from cozy.structures.arrays import TArray
from cozy.structures import extension_handler
from cozy.syntax import *

from .misc import *

JAVA_PRIMITIVE_TYPES = {"boolean", "byte", "char", "short", "int", "long", "float", "double"}

def bracketed(s: str):
    return "{\n" + "\n".join(["\t" + line for line in s.split("\n")]) + "\n}"

class JavaPrinter:
    def __init__(self, out):
        self.out = out
        self.unique_counter = 0
        self.needs_aux = {}
    
    def fresh_temporary(self, name = "temp"):
        self.unique_counter += 1
        return "{}{}".format(name, self.unique_counter)

    def render_complete(self, *, spec: Spec, state_map, share_info, abstract_state):
        if len(share_info) != 0:
            raise NotImplemented
        
        # debug(impl)
        example_spec = Spec(
            # name
            'Basic',
            # types
            [],
            # extern_funcs
            [],
            # statevars 
            [
                ('_var27', TBag(TInt())),
                ('_var2428', TMap(TInt(), TBool())),
                ('_var14938', TMap(TInt(), TInt())),
            ],
            # assumptions
            [],
            # methods 
            [
                Query('elems', 'public', [], (), EVar('_var27').with_type(TBag(TInt())), ''),
                Query('_query42', 'internal', [('n', TInt())], (), ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), '[add] additions to _var27'),
                Query('_query43', 'internal', [('n', TInt())], (), EEmptyList().with_type(TBag(TInt())), '[add] deletions from _var27'),
                Query('_query92', 'internal', [('n', TInt())], (), ECond(EHasKey(EVar('_var2428').with_type(TMap(TInt(), TBool())), EVar('n').with_type(TInt())).with_type(TBool()), ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '[remove] deletions from _var27'),
                Query('_query2702', 'internal', [('n', TInt())], (), EFilter(ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), ELambda(EVar('_var2601').with_type(TInt()), EUnaryOp('not', EHasKey(EVar('_var2428').with_type(TMap(TInt(), TBool())), EVar('_var2601').with_type(TInt())).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), '[add] new or modified keys from _var2428'),
                Query('_query3619', 'internal', [('n', TInt())], (), ECond(EBinOp(EMapGet(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('n').with_type(TInt())).with_type(TInt()), '==', ENum(1).with_type(TInt())).with_type(TBool()), ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt())), EEmptyList().with_type(TBag(TInt()))).with_type(TBag(TInt())), '[remove] keys removed from _var2428'),
                Query('_query15748', 'internal', [('n', TInt()), ('_var15437', TInt()), ('_var15438', TInt())], (), EBinOp(EMapGet(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var15437').with_type(TInt())).with_type(TInt()), '+', ENum(1).with_type(TInt())).with_type(TInt()), '[add] new value for _var15438'),
                Query('_query19227', 'internal', [('n', TInt()), ('_var18920', TInt()), ('_var18921', TInt())], (), EBinOp(EVar('_var18921').with_type(TInt()), '-', ENum(1).with_type(TInt())).with_type(TInt()), '[remove] new value for _var18921'),
                Query('_query19231', 'internal', [('n', TInt())], (), EFilter(EUnaryOp('distinct', EBinOp(EVar('_var27').with_type(TBag(TInt())), '-', ESingleton(EVar('n').with_type(TInt())).with_type(TBag(TInt()))).with_type(TBag(TInt()))).with_type(TBag(TInt())), ELambda(EVar('_var18920').with_type(TInt()), EBinOp(EBool(False).with_type(TBool()), 'or', EUnaryOp('not', EBinOp(EMapGet(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var18920').with_type(TInt())).with_type(TInt()), '==', EUnaryOp('len', EFilter(EFilter(EVar('_var27').with_type(TBag(TInt())), ELambda(EVar('_var65248').with_type(TInt()), EUnaryOp('not', EBinOp(EVar('_var65248').with_type(TInt()), '==', EVar('n').with_type(TInt())).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), ELambda(EVar('_var13489').with_type(TInt()), EBinOp(EVar('_var18920').with_type(TInt()), '==', EVar('_var13489').with_type(TInt())).with_type(TBool()))).with_type(TBag(TInt()))).with_type(TInt())).with_type(TBool())).with_type(TBool())).with_type(TBool()))).with_type(TBag(TInt())), '[remove] new or modified keys from _var14938'),
                Op('add', [('n', TInt())], [], SSeq(SSeq(SDecl('_var220817', ECall('_query2702', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt()))), SDecl('_var220819', EMakeMap2(ECall('_query42', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), ELambda(EVar('_var15437').with_type(TInt()), ECall('_query15748', (EVar('n').with_type(TInt()), EVar('_var15437').with_type(TInt()), EMapGet(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var15437').with_type(TInt())).with_type(TInt()))).with_type(TInt()))).with_type(TMap(TInt(), TInt())))), SSeq(SSeq(SForEach(EVar('_var2601').with_type(TInt()), ECall('_query43', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SMapDel(EVar('_var2428').with_type(TMap(TInt(), TBool())), EVar('_var2601').with_type(TInt()))), SForEach(EVar('_var2601').with_type(TInt()), EVar('_var220817').with_type(TBag(TInt())), SMapUpdate(EVar('_var2428').with_type(TMap(TInt(), TBool())), EVar('_var2601').with_type(TInt()), EVar('_var2602').with_type(TBool()), SNoOp()))), SSeq(SSeq(SForEach(EVar('_var15437').with_type(TInt()), ECall('_query43', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SMapDel(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var15437').with_type(TInt()))), SForEach(EVar('_var15437').with_type(TInt()), ECall('_query42', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SMapUpdate(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var15437').with_type(TInt()), EVar('_var15438').with_type(TInt()), SAssign(EVar('_var15438').with_type(TInt()), EMapGet(EVar('_var220819').with_type(TMap(TInt(), TInt())), EVar('_var15437').with_type(TInt())).with_type(TInt()))))), SSeq(SForEach(EVar('_var44').with_type(TInt()), ECall('_query43', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SCall(EVar('_var27').with_type(TBag(TInt())), 'remove', (EVar('_var44').with_type(TInt()),))), SForEach(EVar('_var44').with_type(TInt()), ECall('_query42', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SCall(EVar('_var27').with_type(TBag(TInt())), 'add', (EVar('_var44').with_type(TInt()),))))))), ''),
                Op('remove', [('n', TInt())], [], SSeq(SSeq(SDecl('_var220820', ECall('_query3619', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt()))), SSeq(SDecl('_var220821', ECall('_query19231', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt()))), SDecl('_var220822', ECall('_query92', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt()))))), SSeq(SSeq(SForEach(EVar('_var3617').with_type(TInt()), ECall('_query3619', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SMapDel(EVar('_var2428').with_type(TMap(TInt(), TBool())), EVar('_var3617').with_type(TInt()))), SForEach(EVar('_var3617').with_type(TInt()), ECall('_query43', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SMapUpdate(EVar('_var2428').with_type(TMap(TInt(), TBool())), EVar('_var3617').with_type(TInt()), EVar('_var3618').with_type(TBool()), SNoOp()))), SSeq(SSeq(SForEach(EVar('_var18920').with_type(TInt()), EVar('_var220820').with_type(TBag(TInt())), SMapDel(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var18920').with_type(TInt()))), SForEach(EVar('_var18920').with_type(TInt()), EVar('_var220821').with_type(TBag(TInt())), SMapUpdate(EVar('_var14938').with_type(TMap(TInt(), TInt())), EVar('_var18920').with_type(TInt()), EVar('_var18921').with_type(TInt()), SAssign(EVar('_var18921').with_type(TInt()), ECall('_query19227', (EVar('n').with_type(TInt()), EVar('_var18920').with_type(TInt()), EVar('_var18921').with_type(TInt()))).with_type(TInt()))))), SSeq(SForEach(EVar('_var93').with_type(TInt()), EVar('_var220822').with_type(TBag(TInt())), SCall(EVar('_var27').with_type(TBag(TInt())), 'remove', (EVar('_var93').with_type(TInt()),))), SForEach(EVar('_var93').with_type(TInt()), ECall('_query43', (EVar('n').with_type(TInt()),)).with_type(TBag(TInt())), SCall(EVar('_var27').with_type(TBag(TInt())), 'add', (EVar('_var93').with_type(TInt()),))))))), ''),
            ],
            # header
            '',
            # footer
            '',
            # docstring
            ''
        )
        if len(spec.types) > 0:
            raise NotImplemented
        if len(spec.extern_funcs) > 0:
            raise NotImplemented
        if len(spec.assumptions) > 0:
            raise NotImplemented
        if len(spec.header) > 0:
            raise NotImplemented
        if len(spec.footer) > 0:
            raise NotImplemented
        if len(spec.docstring) > 0:
            raise NotImplemented
        # debug(state_map)
        example_state_map = OrderedDict([
            (
                '_var27',
                EVar('l').with_type(TBag(TInt()))
            ),
            (
                '_var2428',
                EMakeMap2(
                    EVar('l').with_type(TBag(TInt())),
                    ELambda(EVar('_var2010').with_type(TInt()), EBool(True).with_type(TBool()))
                ).with_type(TMap(TInt(), TBool()))
            ),
            (
                '_var14938',
                EMakeMap2(
                    EVar('l').with_type(TBag(TInt())),
                    ELambda(
                        EVar('_var13488').with_type(TInt()),
                        EUnaryOp('len',
                            EFilter(
                                EVar('l').with_type(TBag(TInt())),
                                ELambda(
                                    EVar('_var13489').with_type(TInt()),
                                    EBinOp(EVar('_var13488').with_type(TInt()), '==', EVar('_var13489').with_type(TInt())).with_type(TBool())
                                )
                            ).with_type(TBag(TInt()))
                        ).with_type(TInt())
                    )
                ).with_type(TMap(TInt(), TInt()))
            ),
        ])
        
        # debug(share_info)
        # defaultdict(<class 'list'>, {})
        if len(share_info) > 0:
            raise NotImplemented
        
        # debug(abstract_state)
        # [('l', TBag(TInt()))]


        self.out.write("class {name} {body}".format(
            name = spec.name,
            body = bracketed(self.render_spec(spec)),
        ))
    
    def render_spec(self, spec: Spec):
        out = ""

        out += "// state vars\n"
        for statevar in spec.statevars:
            out += self.render_statevar(statevar) + "\n"
        
        out += "// methods\n"
        for method in spec.methods:
            if type(method) is Query:
                out += self.render_query(method) + "\n"
            elif type(method) is Op:
                out += self.render_op(method) + "\n"
            else:
                raise NotImplementedError

        for need in self.needs_aux:
            out += "// needs auxilliary '{}'\n".format(need)

        return out
    
    def render_query(self, query: Query):
        visibility = "private"
        if query.visibility == "public":
            visibility = "public"
        return "{visibility} {name}({args}) {body}".format(
            name = query.name,
            args = self.render_args(query.args),
            body = self.render_expr_return_block(query.ret),
            visibility = visibility,
        )
    
    def combine_code(self, *args):
        pieces = [piece for piece in args if piece is not None]
        if len(pieces) == 0:
            return None
        return "\n".join(pieces)

    def render_expr(self, expr: Exp, mapping) -> Tuple[Optional[str], str]:
        # returns a pair of (setup_code, inline_string).
        # The setup code is several statements, and the inline_string is one Java expression.
        if type(expr) is EVar:
            if expr.id in mapping:
                return None, mapping[expr.id]
            return None, "{}".format(expr.id)
        elif type(expr) is ECall:
            pieces = [self.render_expr(arg, mapping) for arg in expr.args]
            setups = [s[0] for s in pieces if s[0] is not None]
            if len(setups) == 0:
                setups = None
            else:
                setups = "\n".join(setups)
            inlines = [s[1] for s in pieces]
            return setups, "{}({})".format(expr.func, ", ".join(inlines))
        elif type(expr) is EBinOp:
            if expr.op == "or":
                if type(expr.e1) is EBool:
                    if expr.e1.val:
                        # absorbs
                        return self.render_expr(expr.e1, mapping)
                    else:
                        # identity
                        return self.render_expr(expr.e2, mapping)
                if type(expr.e2) is EBool:
                    if expr.e2.val:
                        # absorbs
                        return self.render_expr(expr.e2, mapping)
                    else:
                        # identity
                        return self.render_expr(expr.e1, mapping)
            (left_setup, left_inline) = self.render_expr(expr.e1, mapping)
            (right_setup, right_inline) = self.render_expr(expr.e2, mapping)
            if expr.op == "-" and type(expr.e1.type) is TBag:
                self.needs_aux["bagDifference"] = True
                return self.combine_code(left_setup, right_setup), "bagDifference({}, {})".format(left_inline, right_inline)
            op = expr.op
            replace = {
                "or": "||",
                "and": "&&",
            }
            if op in replace:
                op = replace[op]
            return self.combine_code(left_setup, right_setup), "({} {} {})".format(left_inline, op, right_inline)
        elif type(expr) is EUnaryOp:
            arg_setup, arg_inline = self.render_expr(expr.e, mapping)
            if expr.op == "distinct" and type(expr.e.type) is TBag:
                self.needs_aux["bagDistinct"] = True
                return arg_setup, "bagDistinct({})".format(arg_inline)
            if expr.op == "not":
                if type(expr.e) is EBinOp and expr.e.op == "==":
                    return self.render_expr(EBinOp(expr.e.e1, "!=", expr.e.e2).with_type(expr.type), mapping)
                return arg_setup, "(!" + arg_inline + ")"
            if expr.op == "len":
                return arg_setup, "{}.size()".format(arg_inline)
            return arg_setup, "(" + expr.op + " " + arg_inline + ")"
        elif type(expr) is EBool:
            if expr.val:
                return None, "true"
            else:
                return None, "false"
        elif type(expr) is ECond:
            cond_setup, cond_inline = self.render_expr(expr.cond, mapping)
            then_setup, then_inline = self.render_expr(expr.then_branch, mapping)
            else_setup, else_inline = self.render_expr(expr.else_branch, mapping)
            fresh = self.fresh_temporary()
            return self.combine_code(cond_setup, "{temp_type} {temp_name};\nif ({cond_inline}) {then_branch} else {else_branch}".format(
                temp_name = fresh,
                temp_type = self.render_type(expr.type),
                cond_inline = cond_inline,
                then_branch = bracketed(self.combine_code(then_setup, "{} = {};".format(fresh, then_inline))),
                else_branch = bracketed(self.combine_code(else_setup, "{} = {};".format(fresh, else_inline))),
            )), fresh
        elif type(expr) is EHasKey:
            map_setup, map_inline = self.render_expr(expr.map, mapping)
            key_setup, key_inline = self.render_expr(expr.key, mapping)
            return self.combine_code(map_setup, key_setup), "{}.containsKey({})".format(map_inline, key_inline)
        elif type(expr) is ELambda:
            raise RuntimeError("unexpected bare ELambda (should only occur in map/filter)")
        elif type(expr) is EMapGet:
            map_setup, map_inline = self.render_expr(expr.map, mapping)
            key_setup, key_inline = self.render_expr(expr.key, mapping)
            return self.combine_code(map_setup, key_setup), "{}.get({})".format(map_inline, key_inline)
        elif type(expr) is ENum:
            return None, "{}".format(expr.val)
        elif type(expr) is ESingleton:
            singleton = self.fresh_temporary("singleton")
            item_setup, item_inline = self.render_expr(expr.e, mapping)
            return self.combine_code(
                item_setup,
                "{type} {name} = new {type}();".format(type = self.render_type(expr.type), name = singleton),
                "{name}.add({item});".format(name = singleton, item = item_inline),
            ), singleton
        elif type(expr) is EFilter:
            # first, build the bag
            bag_setup, bag_inline = self.render_expr(expr.e, mapping)
            if type(expr.p) is not ELambda:
                raise RuntimeError("EFilter with non-lambda filter")
            result = self.fresh_temporary("filtered")
            item = self.fresh_temporary("item")

            new_mapping = {}
            for v in mapping:
                new_mapping[v] = mapping[v]
            new_mapping[expr.p.arg.id] = item
            lambda_setup, lambda_inline = self.render_expr(expr.p.body, new_mapping)
            item_addition_code = self.combine_code(lambda_setup, "if ({cond}) {open_brace}\n\t{col}.add({item});\n{close_brace}".format(cond = lambda_inline, col = result, open_brace="{", close_brace="}", item = item))
            filtering_code = "{result_type} {result} = new {result_type}();\nfor ({item_type} {item} : {bag_inline}) {inside}".format(
                result_type = self.render_type(expr.type),
                bag_inline = bag_inline,
                item_type = self.render_type(expr.type.t),
                result = result,
                item = item,
                inside = bracketed(item_addition_code),
            )
            return self.combine_code(bag_setup, filtering_code), result
        elif type(expr) is EMakeMap2:
            if type(expr.value) is not ELambda:
                raise NotImplementedError
            make = self.fresh_temporary("make")
            keys_setup, keys_inline = self.render_expr(expr.e, mapping)
            
            key = self.fresh_temporary("key")
            new_mapping = {}
            for v in mapping:
                new_mapping[v] = mapping[v]
            new_mapping[expr.value.arg.id] = key

            val_setup, val_inline = self.render_expr(expr.value.body, new_mapping)
            body = bracketed(self.combine_code(
                val_setup,
                "{}.set({}, {});".format(make, key, val_inline)
            ))
            return self.combine_code(
                keys_setup,
                "{map_type} {make} = new {map_type}();".format(
                    map_type = self.render_type(expr.type),
                    make = make,
                ),
                "for ({key_type} {key_name} : {keys}) {body}".format(
                    key_type = self.render_type(expr.value.arg.type),
                    key_name = key,
                    keys = keys_inline,
                    body = body,
                ),
            ), make
        elif type(expr) is EEmptyList:
            return None, "new {}()".format(self.render_type(expr.type))
        else:
            debug(expr)
            raise NotImplementedError
    def render_expr_return_block(self, expr: Exp):
        (setup, inline) = self.render_expr(expr, {})
        return bracketed(self.combine_code(setup, "return {};".format(inline)))

    def render_stmt(self, stmt: Stm):
        if type(stmt) is SAssign:
            if type(stmt.lhs) is not EVar:
                raise NotImplementedError
            rhs_setup, rhs_inline = self.render_expr(stmt.rhs, {})
            return self.combine_code(rhs_setup, "{} = {};".format(stmt.lhs.id, rhs_inline))
        elif type(stmt) is SCall:
            if type(stmt.target) is not EVar:
                raise NotImplementedError
            call_setup, call_inline = self.render_expr(ECall(stmt.func, stmt.args).with_type(stmt.target.type), {})
            return self.combine_code(call_setup, "{} = {};".format(stmt.target.id, call_inline))
        elif type(stmt) is SDecl:
            init_setup, init_inline = self.render_expr(stmt.val, {})
            return self.combine_code(init_setup, "{} {} = {};".format(self.render_type(stmt.val.type), stmt.id, init_inline))
        elif type(stmt) is SForEach:
            iter_setup, iter_inline = self.render_expr(stmt.iter, {})
            return self.combine_code(
                iter_setup,
                "for ({} {} : {}) {}".format(self.render_type(stmt.id.type), stmt.id.id, iter_inline, bracketed(self.render_stmt(stmt.body))),
            )
        elif type(stmt) is SMapDel:
            map_setup, map_inline = self.render_expr(stmt.map, {})
            key_setup, key_inline = self.render_expr(stmt.key, {})
            return self.combine_code(
                map_setup,
                key_setup,
                "{}.remove({});".format(map_inline, key_inline),
            )
        elif type(stmt) is SMapUpdate:
            map_setup, map_inline = self.render_expr(stmt.map, {})
            key_setup, key_inline = self.render_expr(stmt.key, {})
            modify = self.render_stmt(stmt.change)
            return self.combine_code(
                map_setup,
                key_setup,
                "{} {} = {}.get({});".format(self.render_type(stmt.val_var.type), stmt.val_var.id, map_inline, key_inline),
                modify,
                "{}.set({}, {});".format(map_inline, key_inline, stmt.val_var.id),
            )
        elif type(stmt) is SNoOp:
            return "/* no-op */"
        elif type(stmt) is SSeq:
            return self.combine_code(self.render_stmt(stmt.s1), self.render_stmt(stmt.s2))
        else:
            raise NotImplementedError

    def render_args(self, args):
        if len(args) == 0:
            return ""
        return ", ".join([self.render_arg(arg) for arg in args])
    
    def render_arg(self, arg: Tuple[str, Type]):
        return "{type} {name}".format(
            type = self.render_type(arg[1]),
            name = arg[0],
        )
    
    def render_op(self, op: Op):
        if len(op.assumptions) > 0:
            raise NotImplementedError
        if len(op.docstring) > 0:
            raise NotImplementedError
        return "public {name}({args}) {body}".format(
            name = op.name,
            args = self.render_args(op.args),
            body = bracketed(self.render_stmt(op.body)),
        )

    def render_statevar(self, statevar: Tuple[str, Type]):
        return "private {type} {name};".format(name = statevar[0], type = self.render_type(statevar[1]))
    
    def render_type(self, atype: Type):
        if type(atype) is TInt:
            return "Integer" # TODO: allow unboxed types when possible
        elif type(atype) is TLong:
            raise NotImplementedError
        elif type(atype) is TFloat:
            raise NotImplementedError
        elif type(atype) is TBool:
            return "Boolean" # TODO: allow unboxed types when possible.
        elif type(atype) is TString:
            return "String"
        elif type(atype) is TNative:
            raise NotImplementedError
        elif type(atype) is THandle:
            raise NotImplementedError
        elif type(atype) is TBag:
            # not really precise, but only sane implementation
            return "java.util.ArrayList<{item}>".format(item = self.render_type(atype.t))
        elif type(atype) is TSet:
            return "java.util.HashSet<{key}>".format(key = self.render_type(atype.t))
        elif type(atype) is TList:
            return "java.util.ArrayList<{item}>".format(item = self.render_type(atype.t))
        elif type(atype) is TMap:
            return "java.util.HashMap<{key}, {val}>".format(key = self.render_type(atype.k), val = self.render_type(atype.v))
        elif type(atype) is TNamed:
            raise NotImplementedError
        elif type(atype) is TRecord:
            raise NotImplementedError
        elif type(atype) is TApp:
            raise NotImplementedError
        elif type(atype) is TEnum:
            raise NotImplementedError
        elif type(atype) is TTuple:
            raise NotImplementedError
        else:
            raise NotImplementedError





