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

def combine_code(*args):
    pieces = [piece for piece in args if piece is not None]
    if len(pieces) == 0:
        return None
    return "\n".join(pieces)

def bracketed(*args):
    return "{\n" + "\n".join(["\t" + line for line in combine_code(*args).split("\n")]) + "\n}"

class RenderedExpr:
    def __init__(self, *, inline, setup = None):
        self.setup = setup
        self.inline = inline
    def use(self, func):
        subrender = func(self.inline)
        return RenderedExpr(
            setup = combine_code(self.setup, subrender.setup),
            inline = subrender.inline,
        )

def rendered_expr_list(input):
    return RenderedExpr(
        setup = combine_code(*[item.setup for item in input]),
        inline = [item.inline for item in input]
    )

class JavaPrinter:
    def __init__(self, out):
        self.out = out
        self.unique_counter = 0
        self.needs_aux = {}
    
    def fresh_temporary(self, name = "temp"):
        self.unique_counter += 1
        return "{}{}".format(name, self.unique_counter)

    def render_complete(self, *, spec: Spec, state_map, share_info, abstract_state):
        debug(spec)
        debug(share_info)
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
        if len(spec.extern_funcs) > 0:
            raise NotImplementedError
        if len(spec.assumptions) > 0:
            raise NotImplementedError
        if len(spec.header) > 0:
            raise NotImplementedError
        if len(spec.footer) > 0:
            raise NotImplementedError
        if len(spec.docstring) > 0:
            raise NotImplementedError
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
        out += "// types\n"
        for (name, custom) in spec.types:
            if type(custom.value_type) is not TRecord:
                raise NotImplementedError
            record = custom.value_type
            out += "class {} {}\n".format(name, "{")
            for (fieldname, fieldtype) in record.fields:
                out += "\tpublic {} {};\n".format(self.render_type(fieldtype), fieldname)
            out += "\t{}(".format(name)
            out += ", ".join([self.render_type(fieldtype) + " " + fieldname for (fieldname, fieldtype) in record.fields])
            out += ") {\n"
            for (fieldname, fieldtype) in record.fields:
                out += "\t\tthis.{f} = {f};\n".format(f = fieldname)
            out += "\t}\n"
            out += "}\n"
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

    def render_expr(self, expr: Exp, mapping) -> RenderedExpr:
        # returns a pair of (setup_code, inline_string).
        # The setup code is several statements, and the inline_string is one Java expression.
        if type(expr) is EVar:
            if expr.id in mapping:
                return RenderedExpr(inline = mapping[expr.id])
            return RenderedExpr(inline = "{}".format(expr.id))
        elif type(expr) is ECall:
            return rendered_expr_list([self.render_expr(arg, mapping) for arg in expr.args]).use(lambda args:
                RenderedExpr(inline = "{}({})".format(expr.func, ", ".join(args)))
            )
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
            # TODO: deal specially with "-" when they're TBag. (see needs_aux)
            def correct_op():
                if expr.op == "or":
                    return "||"
                if expr.op == "and":
                    return "&&"
                return expr.op
            return self.render_expr(expr.e1, mapping).use(lambda left:
                self.render_expr(expr.e2, mapping).use(lambda right:
                    RenderedExpr(inline = "({} {} {})".format(left, correct_op(), right))
                )
            )
        elif type(expr) is EUnaryOp:
            template = "({op} {arg})"
            if expr.op == "len":
                template = "{arg}.size()"
            if expr.op == "not":
                if type(expr.e) is EBinOp and expr.e.op == "==":
                    return self.render_expr(EBinOp(expr.e.e1, "!=", expr.e.e2).with_type(expr.type), mapping)
                template = "(!{arg})"
            return self.render_expr(expr.e, mapping).use(lambda val:
                RenderedExpr(inline = template.format(arg = val, op = expr.op))
            )
        elif type(expr) is EGetField:
            return self.render_expr(expr.e, mapping).use(
                lambda obj: RenderedExpr(inline = obj + "." + expr.f)
            )
        elif type(expr) is EMakeRecord:
            return rendered_expr_list([self.render_expr(field, mapping) for field in expr.fields]).use(lambda fields:
                RenderedExpr(inline = "new {}({})".format(expr.type.state_var, ", ".join(fields)))
            )
        elif type(expr) is EBool:
            if expr.val:
                return RenderedExpr(inline = "true")
            else:
                return RenderedExpr(inline = "false")
        elif type(expr) is ECond:
            fresh = self.fresh_temporary()
            cond = self.render_expr(expr.cond, mapping)
            then_branch = self.render_expr(expr.then_branch, mapping)
            else_branch = self.render_expr(expr.else_branch, mapping)
            # TODO: refactor this is we can 
            return RenderedExpr(
                setup = combine_code(cond.setup, "{temp_type} {temp_name};\nif ({cond_inline}) {then_branch} else {else_branch}".format(
                    temp_name = fresh,
                    temp_type = self.render_type(expr.type),
                    cond_inline = cond.inline,
                    then_branch = bracketed(combine_code(then_branch.setup, "{} = {};".format(fresh, then_branch.inline))),
                    else_branch = bracketed(combine_code(else_branch.setup, "{} = {};".format(fresh, else_branch.inline))),
                )),
                inline = fresh
            )
        elif type(expr) is EHasKey:
            return self.render_expr(expr.map, mapping).use(lambda m:
                self.render_expr(expr.key, mapping).use(lambda k:
                    RenderedExpr(inline = "{}.containsKey({})".format(m, k))
                )
            )
        elif type(expr) is ELambda:
            raise RuntimeError("unexpected bare ELambda (should only occur in map/filter)")
        elif type(expr) is EMapGet:
            return self.render_expr(expr.map, mapping).use(lambda m:
                self.render_expr(expr.key, mapping).use(lambda k:
                    RenderedExpr(inline = "{}.get({})".format(map_inline, key_inline))
                )
            )
        elif type(expr) is ENum:
            return RenderedExpr(inline = "{}".format(expr.val))
        elif type(expr) is ESingleton:
            singleton = self.fresh_temporary("singleton")
            return self.render_expr(expr.e, mapping).use(lambda item:
                RenderedExpr(
                    setup = combine_code(
                        "{type} {name} = new {type}();".format(type = self.render_type(expr.type), name = singleton),
                        "{name}.add({item});".format(name = singleton, item = item),
                    ),
                    inline = singleton,
                )
            ) 
        elif type(expr) is EFilter:
            # first, build the bag
            bag = self.render_expr(expr.e, mapping)
            if type(expr.p) is not ELambda:
                raise RuntimeError("EFilter with non-lambda filter")
            result = self.fresh_temporary("filtered")
            item = self.fresh_temporary("item")

            new_mapping = {}
            for v in mapping:
                new_mapping[v] = mapping[v]
            new_mapping[expr.p.arg.id] = item
            lambda_body = self.render_expr(expr.p.body, new_mapping)
            item_addition_code = combine_code(lambda_body.setup, "if ({cond}) {open_brace}\n\t{col}.add({item});\n{close_brace}".format(cond = lambda_body.inline, col = result, open_brace="{", close_brace="}", item = item))
            filtering_code = "{result_type} {result} = new {result_type}();\nfor ({item_type} {item} : {bag_inline}) {inside}".format(
                result_type = self.render_type(expr.type),
                bag_inline = bag.inline,
                item_type = self.render_type(expr.type.t),
                result = result,
                item = item,
                inside = bracketed(item_addition_code),
            )
            return RenderedExpr(setup = combine_code(bag.setup, filtering_code), inline = result)
        elif type(expr) is EMap:
            # first, build the bag
            bag = self.render_expr(expr.e, mapping)
            if type(expr.f) is not ELambda:
                raise RuntimeError("EMap with non-lambda filter")
            result = self.fresh_temporary("mapped")
            item = self.fresh_temporary("item")

            new_mapping = {}
            for v in mapping:
                new_mapping[v] = mapping[v]
            new_mapping[expr.f.arg.id] = item
            lambda_body = self.render_expr(expr.f.body, new_mapping)
            item_addition_code = combine_code(lambda_body.setup, "{result}.add({item});".format(result = result, item = lambda_body.inline))
            filtering_code = "{result_type} {result} = new {result_type}();\nfor ({item_type} {item} : {bag_inline}) {inside}".format(
                result_type = self.render_type(expr.type),
                bag_inline = bag.inline,
                item_type = self.render_type(expr.type.t),
                result = result,
                item = item,
                inside = bracketed(item_addition_code),
            )
            return RenderedExpr(setup = combine_code(bag.setup, filtering_code), inline = result)
        elif type(expr) is EMakeMap2:
            if type(expr.value) is not ELambda:
                raise NotImplementedError
            make = self.fresh_temporary("make")
            keys = self.render_expr(expr.e, mapping)
            
            key = self.fresh_temporary("key")
            new_mapping = {}
            for v in mapping:
                new_mapping[v] = mapping[v]
            new_mapping[expr.value.arg.id] = key

            val = self.render_expr(expr.value.body, new_mapping)
            body = bracketed(combine_code(
                val.setup,
                "{}.set({}, {});".format(make, key, val.inline)
            ))
            return RenderedExpr(
                setup = combine_code(
                    keys.setup,
                    "{map_type} {make} = new {map_type}();".format(
                        map_type = self.render_type(expr.type),
                        make = make,
                    ),
                    "for ({key_type} {key_name} : {keys}) {body}".format(
                        key_type = self.render_type(expr.value.arg.type),
                        key_name = key,
                        keys = keys.inline,
                        body = body,
                    ),
                ),
                inline = make,
            )
        elif type(expr) is EEmptyList:
            return RenderedExpr(inline = "new {}()".format(self.render_type(expr.type)))
        
        debug(expr)
        raise NotImplementedError
    def render_expr_return_block(self, expr: Exp):
        rendered = self.render_expr(expr, {})
        return bracketed(combine_code(rendered.setup, "return {};".format(rendered.inline)))

    def render_stmt(self, stmt: Stm):
        if type(stmt) is SAssign:
            if type(stmt.lhs) is not EVar:
                raise NotImplementedError
            rhs = self.render_expr(stmt.rhs, {})
            return combine_code(rhs.setup, "{} = {};".format(stmt.lhs.id, rhs.inline))
        elif type(stmt) is SCall:
            if type(stmt.target) is not EVar:
                raise NotImplementedError
            call = self.render_expr(ECall(stmt.func, stmt.args).with_type(stmt.target.type), {})
            return combine_code(call.setup, "{} = {};".format(stmt.target.id, call.inline))
        elif type(stmt) is SDecl:
            debug(stmt.val)
            init = self.render_expr(stmt.val, {})
            return combine_code(init.setup, "{} {} = {};".format(self.render_type(stmt.val.type), stmt.id, init.inline))
        elif type(stmt) is SForEach:
            iter_block = self.render_expr(stmt.iter, {})
            return combine_code(
                iter_block.setup,
                "for ({} {} : {}) {}".format(self.render_type(stmt.id.type), stmt.id.id, iter_block.inline, bracketed(self.render_stmt(stmt.body))),
            )
        elif type(stmt) is SMapDel:
            map_obj = self.render_expr(stmt.map, {})
            key = self.render_expr(stmt.key, {})
            return combine_code(
                map_obj.setup,
                key.setup,
                "{}.remove({});".format(map_obj.inline, key.inline),
            )
        elif type(stmt) is SMapUpdate:
            map_obj = self.render_expr(stmt.map, {})
            key = self.render_expr(stmt.key, {})
            modify = self.render_stmt(stmt.change)
            return combine_code(
                map_obj.setup,
                key.setup,
                "{} {} = {}.get({});".format(self.render_type(stmt.val_var.type), stmt.val_var.id, map_obj.inline, key.inline),
                modify,
                "{}.set({}, {});".format(map_obj.inline, key.inline, stmt.val_var.id),
            )
        elif type(stmt) is SNoOp:
            return "/* no-op */"
        elif type(stmt) is SSeq:
            return combine_code(self.render_stmt(stmt.s1), self.render_stmt(stmt.s2))
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
            return atype.statevar # TODO: this is a terrible name
        elif type(atype) is TBag:
            # TODO: make it a HashMap<{item}, Integer>.
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
