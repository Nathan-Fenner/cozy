from collections import OrderedDict
from typing import *

from cozy.target_syntax import *
from cozy.structures.arrays import TArray
from cozy.structures import extension_handler
from cozy.syntax import *

from .misc import *

java_builtins = """
public static final class Bag<T> implements java.lang.Iterable<T> {
    private final java.util.HashMap<T, Integer> hash;
    Bag() {
        hash = new java.util.HashMap<T, Integer>();
    }
    pubic final void add(T item) {
        if (hash.containsKey(item)) {
            hash.replace(item, hash.get(item) + 1);
        } else {
            hash.put(item, 1);
        }
    }
    public final void remove(T item) {
        if (hash.containsKey(item)) {
            if (hash.get(item) == 1) {
                hash.remove(item);
            } else {
                hash.put(item, hash.get(item)-1);
            }
        }
    }
    public final bool contains(T item) {
        return hash.containsKey(item);
    }
    public final Bag<T> union(Bag<T> other) {
        Bag<T> out = new Bag<T>();
        for (java.util.HashMap.Entry<T, Integer> p : hash.entrySet()) {
            out.hash.put(p.getKey(), p.getValue());
        }
        for (java.util.HashMap.Entry<T, Integer> p : other.hash.entrySet()) {
            if (out.has.containsKey(p.getKey())) {
                out.hash.put(p.getKey(), out.hash.get(p.getKey()) + p.getValue());
            } else {
                out.hash.put(p.getKey(), p.getValue());
            }
        }
        return out;
    }
    public final java.util.HashSet<T> distinct() {
        java.util.HashSet<T> out = new java.util.HashSet<T>();
        for (java.util.HashMap.Entry<T, Integer> p : hash.entrySet()) {
            out.hash.add(p.getKey());
        }
        return out;
    }
    public final Bag<T> difference(Bag<T> other) {
        Bag<T> out = new Bag<T>();
        for (java.util.HashMap.Entry<T, Integer> p : hash.entrySet()) {
            if (other.contains(p.getKey())) {
                if (other.get(p.getKey()) < p.getValue()) {
                    out.hash.put(p.getKey(), p.getValue() - other.get(p.getKey()));
                }
            } else {
                out.hash.put(p.getKey(), p.getValue());
            }
        }
        return out;
    }
    static final class BagIterator<T> implements java.util.Iterator<T> {
        private java.util.HashMap.Entry<T, Integer> current;
        int count;
        private java.util.Iterator<java.util.HashMap.Entry<T, Integer>> iter;
        BagIterator(Bag<T> bag) {
            this.current = null;
            this.count = 0;
            this.iter = bag.hash.entrySet().iterator();
        }
        public boolean hasNext() {
            return (this.current != null && this.count < this.current.getValue()) || this.iter.hasNext();
        }

        public T next() {
            if (this.current == null || this.count >= this.current.getValue()) {
                this.current = this.iter.next();
                this.count = 0;
            }
            this.count++;
            return this.current.getKey();
        }
    }
    public final java.util.Iterator<T> iterator() {
        return new BagIterator<T>(this);
    }
    final boolean equals(Object other) {
        if (other instanceof Bag<T>) {
            return hash.equals(((Bag<T>)other).hash);
        }
        return false;
    }
    final int hashCode() {
        return hash.hashCode();
    }
}
"""

def combine_code(*args):
    pieces = [piece for piece in args if piece is not None]
    if len(pieces) == 0:
        return None
    return "\n".join(pieces)

def bracketed(*args):
    return "{\n" + "\n".join(["    " + line for line in combine_code(*args).split("\n")]) + "\n}"

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

    def render_complete(self, *, spec: Spec, state_map, share_info):
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
        if len(share_info) > 0:
            raise NotImplemented
        self.out.write("class {name} {body}".format(
            name = spec.name,
            body = bracketed(self.render_spec(spec)),
        ))
    
    def visit(self, ):
        pass
    def render_spec(self, spec: Spec):
        out = ""
        out += java_builtins
        if len(spec.types) > 0:
            out += "// types\n"
        for (name, custom) in spec.types:
            if type(custom.value_type) is not TRecord:
                raise NotImplementedError
            record = custom.value_type
            out += "class {} {}\n".format(name, "{")
            for (fieldname, fieldtype) in record.fields:
                out += "    public {} {};\n".format(self.render_type(fieldtype), fieldname)
            out += "    {}(".format(name)
            out += ", ".join([self.render_type(fieldtype) + " " + fieldname for (fieldname, fieldtype) in record.fields])
            out += ") {\n"
            for (fieldname, fieldtype) in record.fields:
                out += "        this.{f} = {f};\n".format(f = fieldname)
            out += "    }\n"
            out += "}\n"
        if len(spec.statevars) > 0:
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
            if expr.op == "-" and type(expr.e1.type) is TBag:
                # TODO: only generate this method if needed.
                # will help, sometimes.
                return self.render_expr(expr.e1, mapping).use(lambda left:
                    self.render_expr(expr.e2, mapping).use(lambda right:
                        RenderedExpr(inline = "{}.subtract({})".format(left, right))
                    )
                )
            if expr.op == "+" and type(expr.e1.type) is TBag:
                # TODO: only generate this method if needed
                return self.render_expr(expr.e1, mapping).use(lambda left:
                    self.render_expr(expr.e2, mapping).use(lambda right:
                        RenderedExpr(inline = "{}.union({})".format(left, right))
                    )
                )
            if expr.op == "in":
                return self.render_expr(expr.e1, mapping).use(lambda item:
                    self.render_expr(expr.e2, mapping).use(lambda collection:
                        RenderedExpr(inline = "{}.contains({})".format(item, collection))
                    )
                )
            if type(expr.e1.type) not in [TInt, TLong, TBool, TFloat]:
                raise NotImplementedError("the operator '{}' is not supported for expressions of type {}".format(expr.op, repr(expr.e1.type)))
            def render_op():
                if expr.op == "or":
                    return "||"
                if expr.op == "and":
                    return "&&"
                return expr.op
            return self.render_expr(expr.e1, mapping).use(lambda left:
                self.render_expr(expr.e2, mapping).use(lambda right:
                    RenderedExpr(inline = "({} {} {})".format(left, render_op(), right))
                )
            )
        elif type(expr) is EUnaryOp:
            if expr.op == "len":
                # TODO: allow alternatives based on type
                template = "{arg}.size()"
            elif expr.op == "empty":
                # TODO: allow faster alternatives based on type
                template = "({arg}.size() == 0)"
            elif expr.op == "distinct":
                if type(expr.e.type) is not TBag:
                    raise NotImplementedError("unary operator 'distinct' is only implemented on bags, but it's applied to {}".format(repr(expr)))
                # TODO: allow alternatives based on type
                template = "{arg}.distinct()"
            elif expr.op == "not":
                if type(expr.e.type) is not TBool:
                    raise NotImplementedError("unary operator 'not' is only implemented on bools, but it's applied to {}".format(repr(expr)))
                if type(expr.e) is EBinOp and expr.e.op == "==":
                    # specialize !(a == b) as a!=b.
                    return self.render_expr(EBinOp(expr.e.e1, "!=", expr.e.e2).with_type(expr.type), mapping)
                template = "(!{arg})"
            elif expr.op == "sum":
                if type(expr.type) not in [TInt, TLong, TFloat]:
                    raise NotImplementedError("unary operator '{}' not implemented on {} of type {}".format(expr.op, repr(expr.e), rep(expr.type)))
                sum_into = self.fresh_temporary("sum")
                sum_type = self.render_type(expr.type)
                item = self.fresh_temporary("term")
                return self.render_expr(expr.e, mapping).use(lambda collection:
                    RenderedExpr(
                        setup = combine_code(
                            "{} {} = 0;".format(sum_type, sum_into),
                            "for ({} {} : {})".format(sum_type, item, collection) + bracketed(
                                "{} += {};".format(sum_into, item)
                            ),
                        ),
                        inline = sum_into,
                    )
                )
            elif expr.op == "all":
                if type(expr.type) not in [TBool]:
                    raise NotImplementedError("unary operator '{}' not implemented on {} of type {}".format(expr.op, repr(expr.e), repr(expr.type)))
                all_into = self.fresh_temporary("all")
                item = self.fresh_temporary("term")
                return self.render_expr(expr.e, mapping).use(lambda collection:
                    RenderedExpr(
                        setup = combine_code(
                            "Boolean {} = true;".format(all_into),
                            "for (Boolean {} : {})".format(item, collection) + bracketed(
                                "{} = {} && {};".format(all_into, all_into, item)
                            ),
                        ),
                        inline = all_into,
                    )
                )
            elif expr.op == "any":
                if type(expr.type) not in [TBool]:
                    raise NotImplementedError("unary operator '{}' not implemented on {} of type {}".format(expr.op, repr(expr.e), repr(expr.type)))
                all_into = self.fresh_temporary("any")
                item = self.fresh_temporary("term")
                return self.render_expr(expr.e, mapping).use(lambda collection:
                    RenderedExpr(
                        setup = combine_code(
                            "Boolean {} = false;".format(all_into),
                            "for (Boolean {} : {})".format(item, collection) + bracketed(
                                "{} = {} || {};".format(all_into, all_into, item)
                            ),
                        ),
                        inline = all_into,
                    )
                )
            elif expr.op == "-":
                template = "(-{arg})"
            else:
                raise NotImplementedError("unary operator '{}' not implemented on {}".format(expr.op, repr(expr.e)))
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
                    RenderedExpr(inline = "{}.get({})".format(m, k))
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
            item_addition_code = combine_code(lambda_body.setup, "if ({cond}) {open_brace}\n    {col}.add({item});\n{close_brace}".format(cond = lambda_body.inline, col = result, open_brace="{", close_brace="}", item = item))
            filtering_code = "{result_type} {result} = new {result_type}();\nfor ({item_type} {item} : {bag_inline}) {inside}".format(
                result_type = self.render_type(expr.type),
                bag_inline = bag.inline,
                item_type = self.render_type(expr.type.t),
                result = result,
                item = item,
                inside = bracketed(item_addition_code),
            )
            return RenderedExpr(setup = combine_code(bag.setup, filtering_code), inline = result)
        elif type(expr) is EArgMin:
            
            if type(expr.f) is not ELambda:
                raise RuntimeError("EFilter with non-lambda filter")
            argmin = self.fresh_temporary("argmin")
            argscore = self.fresh_temporary("score")
            candidate = self.fresh_temporary("candidate")
            candidatescore = self.fresh_temporary("candidate_score")

            item_type = self.render_type(expr.type)
            score_type = self.render_type(expr.f.body.type)
            new_mapping = {}
            for v in mapping:
                new_mapping[v] = mapping[v]
            new_mapping[expr.f.arg.id] = candidate

            collection_rendered = self.render_expr(expr.e, mapping)
            body_rendered = self.render_expr(expr.f.body, new_mapping)

            return RenderedExpr(
                setup = combine_code(
                    collection_rendered.setup,
                    "{} {} = null;".format(item_type, argmin),
                    "{} {} = null;".format(score_type, argscore),
                    "for ({} {} : {}) ".format(item_type, candidate, collection_rendered.inline) + bracketed(
                        body_rendered.setup,
                        "{} {} = {};".format(score_type, candidatescore, body_rendered.inline),
                        "if ({} == null || {} < {}) ".format(argmin, candidatescore, argscore) + bracketed(
                            "{} = {};".format(argmin, candidate),
                            "{} = {};".format(argscore, candidatescore),
                        ),
                    )
                ),
                inline = argmin,
            )
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

        raise NotImplementedError("can't generate code for expression {} of type {}".format(repr(expr), type(expr)))
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
            rendered = self.render_expr(stmt.target, {}).use(lambda target:
                rendered_expr_list([self.render_expr(arg, {}) for arg in stmt.args]).use(lambda args:
                    RenderedExpr(inline = "{}.{}({})".format(target, stmt.func, ", ".join(args)))
                )
            )
            return combine_code(rendered.setup, rendered.inline + ";")
        elif type(stmt) is SDecl:
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
            # We provide our own bag, so that it has a uniform interface.
            return "Bag<{item}>".format(item = self.render_type(atype.t))
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
