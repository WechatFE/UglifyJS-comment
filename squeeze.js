/*Copyright 2010 (c) Mihai Bazon <mihai.bazon@gmail.com>
Based on parse-js (http://marijn.haverbeke.nl/parse-js/).

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

    * Redistributions of source code must retain the above
      copyright notice, this list of conditions and the following
      disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials
      provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER “AS IS” AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
SUCH DAMAGE.*/

//优化AST树，使生成的代码尽可能短
//@raphealguo
//官网记录了优化的内容，但是不一定在squeeze_1里边做的，这里只是列出来方便比对，
//这里分别用序号标明各个规则，在下边源码注释中会使用规则X的字眼来引用。
/*
	1. foo[“bar”] ==> foo.bar
	2. remove block brackets {}
	3. join consecutive var declarations: var a = 10; var b = 20; ==> var a=10,b=20;
	4. resolve simple constant expressions: 1 +2 * 3 ==> 7. We only do the replacement if the result occupies less bytes; for example 1/3 would translate to 0.333333333333, so in this case we don’t replace it.
	5. consecutive statements in blocks are merged into a sequence; in many cases, this leaves blocks with a single statement, so then we can remove the block brackets.
	6. various optimizations for IF statements:
	7. if (foo) bar(); else baz(); ==> foo?bar():baz();
	8. if (!foo) bar(); else baz(); ==> foo?baz():bar();
	9. if (foo) bar(); ==> foo&&bar();
	10. if (!foo) bar(); ==> foo||bar();
	11. if (foo) return bar(); else return baz(); ==> return foo?bar():baz();
	12. if (foo) return bar(); else something(); ==> {if(foo)return bar();something()}
	13. remove some unreachable code and warn about it (code that follows a return, throw, break or continue statement, except function/variable declarations).
	14. act a limited version of a pre-processor (c.f. the pre-processor of C/C++) to allow you to safely replace selected global symbols with specified values. When combined with the optimisations above this can make UglifyJS operate slightly more like a compilation process, in that when certain symbols are replaced by constant values, entire code blocks may be optimised away as unreachable.
*/

var warn = function(){};

//比较ast1跟ast2两棵树 最后生成的代码谁比较短，谁短用谁
function best_of(ast1, ast2) {
    return gen_code(ast1).length > gen_code(ast2[0] == "stat" ? ast2[1] : ast2).length ? ast2 : ast1;
};

//当前块里边的最后一条语句
function last_stat(b) {
    if (b[0] == "block" && b[1] && b[1].length > 0)
        return b[1][b[1].length - 1];
    return b;
}

function aborts(t) {
    if (t) switch (last_stat(t)[0]) {
      case "return":
      case "break":
      case "continue":
      case "throw":
        return true;
    }
};

//看看表达式运算结果是否为布尔类型
function boolean_expr(expr) {
    return ( (expr[0] == "unary-prefix"
              && member(expr[1], [ "!", "delete" ])) ||

             (expr[0] == "binary"
              && member(expr[1], [ "in", "instanceof", "==", "!=", "===", "!==", "<", "<=", ">=", ">" ])) ||

             (expr[0] == "binary"
              && member(expr[1], [ "&&", "||" ])
              && boolean_expr(expr[2])
              && boolean_expr(expr[3])) ||

             //三元运算符
             (expr[0] == "conditional"
              && boolean_expr(expr[2])
              && boolean_expr(expr[3])) ||

             //赋值语句
             (expr[0] == "assign"
              && expr[1] === true
              && boolean_expr(expr[3])) ||

             //逗号表达式
             (expr[0] == "seq"
              && boolean_expr(expr[expr.length - 1]))
           );
};

//看看树枝是不是空树枝
function empty(b) {
    return !b || (b[0] == "block" && (!b[1] || b[1].length == 0));
};

//看看当前AST节点是不是string类型
function is_string(node) {
    return (node[0] == "string" ||

    		//typeof得到结果也是字符串
            node[0] == "unary-prefix" && node[1] == "typeof" ||

            //字符串a+字符串b得到字符串
            node[0] == "binary" && node[1] == "+" &&
            (is_string(node[2]) || is_string(node[3])));
};

//尝试将表达式节点化简
var when_constant = (function(){

    var $NOT_CONSTANT = {};

    // this can only evaluate constant expressions.  If it finds anything
    // not constant, it throws $NOT_CONSTANT.
    //尽可能的把表达式化成计算结果
    //a = 3*4 => a = 12;
    //但是不一定这样优化会有效，例如：
    //a = 1/3 => a = 0.33333可能会变得更长
    function evaluate(expr) {
        switch (expr[0]) {
          case "string":
          case "num":
            return expr[1];//单个数字跟字符串不用化简了
          case "name":
          case "atom":
            switch (expr[1]) {//这里要对字符串转真正的Javascript值才能参与计算
              case "true": return true;
              case "false": return false;
              case "null": return null;
            }
            break;
          case "unary-prefix"://一元操作符
            switch (expr[1]) {
              case "!": return !evaluate(expr[2]);
              case "typeof": return typeof evaluate(expr[2]);
              case "~": return ~evaluate(expr[2]);
              case "-": return -evaluate(expr[2]);
              case "+": return +evaluate(expr[2]);
            }
            break;
          case "binary"://二元操作符
            var left = expr[2], right = expr[3];
            switch (expr[1]) {
              case "&&"         : return evaluate(left) &&         evaluate(right);
              case "||"         : return evaluate(left) ||         evaluate(right);
              case "|"          : return evaluate(left) |          evaluate(right);
              case "&"          : return evaluate(left) &          evaluate(right);
              case "^"          : return evaluate(left) ^          evaluate(right);
              case "+"          : return evaluate(left) +          evaluate(right);
              case "*"          : return evaluate(left) *          evaluate(right);
              case "/"          : return evaluate(left) /          evaluate(right);
              case "%"          : return evaluate(left) %          evaluate(right);
              case "-"          : return evaluate(left) -          evaluate(right);
              case "<<"         : return evaluate(left) <<         evaluate(right);
              case ">>"         : return evaluate(left) >>         evaluate(right);
              case ">>>"        : return evaluate(left) >>>        evaluate(right);
              case "=="         : return evaluate(left) ==         evaluate(right);
              case "==="        : return evaluate(left) ===        evaluate(right);
              case "!="         : return evaluate(left) !=         evaluate(right);
              case "!=="        : return evaluate(left) !==        evaluate(right);
              case "<"          : return evaluate(left) <          evaluate(right);
              case "<="         : return evaluate(left) <=         evaluate(right);
              case ">"          : return evaluate(left) >          evaluate(right);
              case ">="         : return evaluate(left) >=         evaluate(right);
              case "in"         : return evaluate(left) in         evaluate(right);
              case "instanceof" : return evaluate(left) instanceof evaluate(right);
            }
        }
        //其他情况都抛出错误，告诉外界没法化简
        throw $NOT_CONSTANT;
    };

    return function(expr, yes, no) {
        try {
        	//参数将表达式expr化成val
            var val = evaluate(expr), ast;

            //如果能够成功 就到这里
            switch (typeof val) {
              //运算的结果只能是null|string|number|boolean
              case "string": ast =  [ "string", val ]; break;
              case "number": ast =  [ "num", val ]; break;
              case "boolean": ast =  [ "name", String(val) ]; break;//这里是因为计算后的结果可能是 true false 但是对于AST叶子来说 应该是一个name的节点才对
              default:
                if (val === null) { ast = [ "atom", "null" ]; break; }
                //没有认出的类型 抛出错误
                throw new Error("Can't handle constant of type: " + (typeof val));
            }
            return yes.call(expr, ast, val);
        } catch(ex) {
            if (ex === $NOT_CONSTANT) {//如果是真的化简失败
                if (expr[0] == "binary"
                    && (expr[1] == "===" || expr[1] == "!==")
                    && ((is_string(expr[2]) && is_string(expr[3]))
                        || (boolean_expr(expr[2]) && boolean_expr(expr[3])))) {
                	//"a" === "b"  "a" !== "b" 
                	//true === true false !== true
                	//这两种都可以把 
                	// === 变成 == 
                	// !== 变成 !=
                    expr[1] = expr[1].substr(0, 2);
                }
                else if (no && expr[0] == "binary"
                         && (expr[1] == "||" || expr[1] == "&&")) {
                    // the whole expression is not constant but the lval may be...
                	// || &&的短路操作
                    try {
                    	//看看 expr[2] && expr[3] 跟 expr[2] && expr[3]
                    	
                        var lval = evaluate(expr[2]);//如果expr[2]能够化简！
	                        //如果 expr[1] == "&&"
	                        //那么expr就是expr[3] 否则还是说expr[2]
                        expr = ((expr[1] == "&&" && (lval ? expr[3] : lval))    ||

	                        //如果 expr[1] == "||"
	                        //如果 expr[2] == true
	                        //那么expr就是expr[2] 否则是expr[3]
                                (expr[1] == "||" && (lval ? lval    : expr[3])) ||
                                expr);
                    } catch(ex2) {
                    	//不能化简第一个操作数 那就没办法了~
                        // IGNORE... lval is not constant
                    }
                }
                return no ? no.call(expr, expr) : null;
            }
            else throw ex;
        }
    };

})();

function warn_unreachable(ast) {
    if (!empty(ast))
        warn("Dropping unreachable code: " + gen_code(ast, true));
};

//预处理if树枝
/*
	把
    if (x) {
        blah();
        return y;
    }
    foobar();

    变成：
    
    if (x) {
        blah();
        return y;
    } else {
        foobar();
    }
    
    为什么？因为对于IF/ELSE的结构，在squeeze_1会有很多特殊的处理，这里把它强制转成带else分支可能在后续的压缩过程可以得到更好的优化
*/
function prepare_ifs(ast) {
    var w = ast_walker(), walk = w.walk;
    //下边已经解释prepare_ifs要做的事情了

    // In this first pass, we rewrite ifs which abort with no else with an
    // if-else.  For example:
    //
    // if (x) {
    //     blah();
    //     return y;
    // }
    // foobar();
    //
    // is rewritten into:
    //
    // if (x) {
    //     blah();
    //     return y;
    // } else {
    //     foobar();
    // }
    function redo_if(statements) {
        statements = MAP(statements, walk);

        //扫描当前语句块里边的if树枝
        //if的AST树枝是：["if", cond, body, belse]
        for (var i = 0; i < statements.length; ++i) {
            var fi = statements[i];
            if (fi[0] != "if") continue;

            if (fi[3]) continue;//如果有else分支，那不用动

            var t = fi[2];
            /*
				function aborts(t) {
				    if (t) switch (last_stat(t)[0]) {
				      case "return":
				      case "break":
				      case "continue":
				      case "throw":
				        return true;
				    }
				};
			*/
			//看看语句块的最后一句是不是跳转出if
            if (!aborts(t)) continue;

            //为什么这里要walk呢？
            //因为有可能 if((function(){if(xxx){xxx}})()) 在cond里边也可能有if语句
            var conditional = walk(fi[1]);

            //把后边的语句变成一个else的树枝
            var e_body = redo_if(statements.slice(i + 1));

            //如果超过一行语句 需要生成一个block
            var e = e_body.length == 1 ? e_body[0] : [ "block", e_body ];

            //返回优化后的AST树
            return statements.slice(0, i).concat([ [
                fi[0],          // "if"
                conditional,    // conditional
                t,              // then 为什么t不用walk? @unkowned
                e               // else
            ] ]);
        }

        return statements;
    };

    function redo_if_lambda(name, args, body) {
        body = redo_if(body);
        return [ this[0], name, args, body ];
    };

    function redo_if_block(statements) {
        return [ this[0], statements != null ? redo_if(statements) : null ];
    };

    return w.with_walkers({
        "defun": redo_if_lambda,
        "function": redo_if_lambda,
        "block": redo_if_block,
        "splice": redo_if_block,
        "toplevel": function(statements) {
            return [ this[0], redo_if(statements) ];
        },
        "try": function(t, c, f) {
            return [
                this[0],
                redo_if(t),
                c != null ? [ c[0], redo_if(c[1]) ] : null,
                f != null ? redo_if(f) : null
            ];
        }
    }, function() {
        return walk(ast);
    });
}

//优化AST树！使得生成的代码最小化
function squeeze_1(ast, options) {
	//覆盖默认参数
    options = defaults(options, {
        make_seqs   : true,
        dead_code   : true,
        no_warnings : false,
        keep_comps  : true,
        unsafe      : false
    });

    //拿到遍历器
    var w = ast_walker(), walk = w.walk, scope;

    //对表达式取非
    function negate(c) {
    	//得到一个非的表达式
        var not_c = [ "unary-prefix", "!", c ];
        switch (c[0]) {
          case "unary-prefix":
          	//!c的非就是c
            return c[1] == "!" && boolean_expr(c[2]) ? c[2] : not_c;
          case "seq":
          	//a,b,!c的非就是：a,b,c
            c = slice(c);
            c[c.length - 1] = negate(c[c.length - 1]);
            return c;
          case "conditional":
          	//a ? b : c的非就是 a ? !b : !c;
            return best_of(not_c, [ "conditional", c[1], negate(c[2]), negate(c[3]) ]);
          case "binary":
          	//二元操作符的非
            var op = c[1], left = c[2], right = c[3];
            if (!options.keep_comps) switch (op) {
              case "<="  : return [ "binary", ">", left, right ];
              case "<"   : return [ "binary", ">=", left, right ];
              case ">="  : return [ "binary", "<", left, right ];
              case ">"   : return [ "binary", "<=", left, right ];
            }
            switch (op) {
              case "=="  : return [ "binary", "!=", left, right ];
              case "!="  : return [ "binary", "==", left, right ];
              case "===" : return [ "binary", "!==", left, right ];
              case "!==" : return [ "binary", "===", left, right ];
              //a && b 非就是 !a || !b
              //a || b 的非就是 a && b
              case "&&"  : return best_of(not_c, [ "binary", "||", negate(left), negate(right) ]);
              case "||"  : return best_of(not_c, [ "binary", "&&", negate(left), negate(right) ]);
            }
            break;
        }
        //其他情况直接前边加!
        return not_c;
    };

    //条件最短化
    //c ? t : e
    //if (c) {t} else {e}
    function make_conditional(c, t, e) {
        var make_real_conditional = function() {
            if (c[0] == "unary-prefix" && c[1] == "!") {
            	//如果c前边有个!
				//例如：if (!c) { A() } else{ B() } 化简成： c ? B() : A();
				//例如：if (!c) { A() } else{ } 化简成： c || A();
                return e ? [ "conditional", c[2], e, t ] : [ "binary", "||", c[2], t ];
            } else {
				//例如：if (c) { A() } else{ B() } 化简成： c ? A() : B(); 或者 !c ? B() : A()
				//例如：if (c) { A() } else{ } 化简成： c && A();
                return e ? best_of(
                    [ "conditional", c, t, e ],
                    [ "conditional", negate(c), e, t ]
                ) : [ "binary", "&&", c, t ];
            }
        };
        // shortcut the conditional if the expression has a constant value
        return when_constant(c, function(ast, val){
            warn_unreachable(val ? e : t);
            return          (val ? t : e);
        }, make_real_conditional);
    };

    //移除语句块
    //只有语句块里边是1条/0条语句的时候才能移除
    //while(true){ { a(); } }可以化简成为 while(true){ a(); }
    //while(true){ { } }可以化简成为 while(true){ }
    function rmblock(block) {
        if (block != null && block[0] == "block" && block[1]) {
            if (block[1].length == 1)
                block = block[1][0];
            else if (block[1].length == 0)//返回一个空块
                block = [ "block" ];
        }
        return block;
    };

    function _lambda(name, args, body) {
        return [ this[0], name, args, tighten(body, "lambda") ];
    };

    // this function does a few things:
    // 1. discard useless blocks
    // 2. join consecutive var declarations
    // 3. remove obviously dead code
    // 4. transform consecutive statements using the comma operator
    // 5. if block_type == "lambda" and it detects constructs like if(foo) return ... - rewrite like if (!foo) { ... }
    //压缩语句块
    function tighten(statements, block_type) {
        statements = MAP(statements, walk);

        //去除空白的block
        statements = statements.reduce(function(a, stat){
            if (stat[0] == "block") {
                if (stat[1]) {
                    a.push.apply(a, stat[1]);
                }
            } else {
                a.push(stat);
            }
            return a;
        }, []);

        statements = (function(a, prev){
        	//var a;var b;优化成 var a, b;
            statements.forEach(function(cur){
                if (prev && ((cur[0] == "var" && prev[0] == "var") ||
                             (cur[0] == "const" && prev[0] == "const"))) {
                    prev[1] = prev[1].concat(cur[1]);
                } else {
                    a.push(cur);
                    prev = cur;
                }
            });
            return a;
        })([]);

        //--no-dead-code 默认 UglifyJS 将会删除不被用到的代码，传入该参数禁用此功能。
        //dead_code 默认是true
        /*
         	function A(){
				var a;
				return b;
				//这之后的语句考虑忽略掉，但是要看看后边有没有函数声明跟变量声明
				a = 1;
				function B(){}
         	}
     	*/
        if (options.dead_code) statements = (function(a, has_quit){
            statements.forEach(function(st){
                if (has_quit) {
                    if (st[0] == "function" || st[0] == "defun") {
                        a.push(st);
                    }
                    else if (st[0] == "var" || st[0] == "const") {
                        if (!options.no_warnings)
                            warn("Variables declared in unreachable code");
                        st[1] = MAP(st[1], function(def){
                            if (def[1] && !options.no_warnings)
                                warn_unreachable([ "assign", true, [ "name", def[0] ], def[1] ]);
                            return [ def[0] ];
                        });
                        a.push(st);
                    }
                    else if (!options.no_warnings)
                        warn_unreachable(st);
                }
                else {//当前作用域已经到了return语句了 那后边的可以考虑压缩忽略掉
                    a.push(st);
                    if (member(st[0], [ "return", "throw", "break", "continue" ]))
                        has_quit = true;
                }
            });
            return a;
        })([]);

        //当调用 ast_squeeze() 将会合并多个语句块为一个语句块，如 "a=10; b=20; foo()" 将被转换为 "a=10,b=20,foo()"
        //make_seqs默认为true
        //命令参数"--no-seqs"可以让make_seqs = false
        if (options.make_seqs) statements = (function(a, prev) {
            statements.forEach(function(cur){
            	//把连续的表达式语句合并成一个逗号表达式。
            	//stat;stat;stat; => stat,stat,stat;
                if (prev && prev[0] == "stat" && cur[0] == "stat") {
                    prev[1] = [ "seq", prev[1], cur[1] ];
                } else {
                    a.push(cur);
                    prev = cur;
                }
            });
            //块的最后一句是：
            //
            /*
            	stat;
            	return A;
            	可以优化成为
            	return stat, A;
            */
            if (a.length >= 2
                && a[a.length-2][0] == "stat"
                && (a[a.length-1][0] == "return" || a[a.length-1][0] == "throw")
                && a[a.length-1][1])
            {
                a.splice(a.length - 2, 2,
                         [ a[a.length-1][0],
                           [ "seq", a[a.length-2][1], a[a.length-1][1] ]]);
            }
            return a;
        })([]);

        // this increases jQuery by 1K.  Probably not such a good idea after all..
        // part of this is done in prepare_ifs anyway.
        // if (block_type == "lambda") statements = (function(i, a, stat){
        //         while (i < statements.length) {
        //                 stat = statements[i++];
        //                 if (stat[0] == "if" && !stat[3]) {
        //                         if (stat[2][0] == "return" && stat[2][1] == null) {
        //                                 a.push(make_if(negate(stat[1]), [ "block", statements.slice(i) ]));
        //                                 break;
        //                         }
        //                         var last = last_stat(stat[2]);
        //                         if (last[0] == "return" && last[1] == null) {
        //                                 a.push(make_if(stat[1], [ "block", stat[2][1].slice(0, -1) ], [ "block", statements.slice(i) ]));
        //                                 break;
        //                         }
        //                 }
        //                 a.push(stat);
        //         }
        //         return a;
        // })(0, []);

        return statements;
    };

    //对if进行优化
    function make_if(c, t, e) {
    	//if (c) {t} else{e}
    	//尝试对c这个表达式化简~
        return when_constant(c, function(ast, val){
        	//如果c最后可以化简成表达式
        	//如果val == true || false之类的
        	//那就有可以去掉else或者then语句了
        	//@optimize
            if (val) {
	        	/*
	        		if (true){
						A();
	        		}else{
						B();
	        		}
	        		化简成：A();
	        	*/
                t = walk(t);
                warn_unreachable(e);
                return t || [ "block" ];
            } else {
            	/*
	        		if (false){
						A();
	        		}else{
						B();
	        		}
	        		化简成：B();
	        	*/
                e = walk(e);
                warn_unreachable(t);
                return e || [ "block" ];
            }
        }, function() {
        	//c没法化简 那就只能走make_real_if来压缩if树
            return make_real_if(c, t, e);
        });
    };

    //if (c) {t;} else { e; return ; }
    //优化成 if (!c) { e;return; } t;
    function abort_else(c, t, e) {
        var ret = [ [ "if", negate(c), e ] ];
        if (t[0] == "block") {
            if (t[1]) ret = ret.concat(t[1]);
        } else {
            ret.push(t);
        }
        return walk([ "block", ret ]);
    };

    //压缩if树枝
    function make_real_if(c, t, e) {
    	//if (c) { t } else {e}
        c = walk(c);
        t = walk(t);
        e = walk(e);

        //if (cond()) {} else{}
        //可以化简成 cond()
        if (empty(e) && empty(t))
            return [ "stat", c ];

        if (empty(t)) {
	        //if (cond()) {} else{ B() }
	        //可以化简成 if (!cond()) { B() }
            c = negate(c);
            t = e;
            e = null;
        } else if (empty(e)) {
	        //if (cond()) { A() } else{ }
	        //可以化简成 if (cond()) { A() }
            e = null;
        } else {
            // if we have both else and then, maybe it makes sense to switch them?
            (function(){
                var a = gen_code(c);
                var n = negate(c);//对条件c求反
                var b = gen_code(n);
                //尝试把条件求反，如果得到的表达式更短
                //那么反转if跟else块
                if (b.length < a.length) {
                    var tmp = t;
                    t = e;
                    e = tmp;
                    c = n;
                }
            })();
        }

        //按照目前得到的AST树枝是这样：
        var ret = [ "if", c, t, e ];

        //考虑分块操作两个句子的情况，只有一个句子的话丢给make_conditional去考虑

        if (t[0] == "if" && empty(t[3]) && empty(e)) {
        	//嵌套IF的压缩
        	//if (c1) { if (c2) { A() } } else{} 尝试化成这样的AST： if (c1 && c2) { A()}
        	//看看哪个AST生成的代码短，谁短用谁。
            ret = best_of(ret, walk([ "if", [ "binary", "&&", c, t[1] ], t[2] ]));
        }
        else if (t[0] == "stat") {//如果if分支列表是一个语句
            if (e) {
                if (e[0] == "stat")
                	//else也是一个语句，那就搞成条件表达式
                    ret = best_of(ret, [ "stat", make_conditional(c, t[1], e[1]) ]);
                else if (aborts(e))//如果else最后有return等跳转控制的关键字
                    ret = abort_else(c, t, e);
            }
            else {//else为空的情况，也搞成条件表达式
                ret = best_of(ret, [ "stat", make_conditional(c, t[1]) ]);
            }
        }
        else if (e && t[0] == e[0] && (t[0] == "return" || t[0] == "throw") && t[1] && e[1]) {
        	//if (c) { return A(); } else { return B(); }
        	//优化成：return c ? A() : B();
            ret = best_of(ret, [ t[0], make_conditional(c, t[1], e[1] ) ]);
        }
        else if (e && aborts(t)) {
        	//看到prepare_ifs做的操作被这里还原回去了~
            ret = [ [ "if", c, t ] ];
            if (e[0] == "block") {
                if (e[1]) ret = ret.concat(e[1]);
            }
            else {
                ret.push(e);
            }
            ret = walk([ "block", ret ]);
        }
        else if (t && aborts(e)) {
            ret = abort_else(c, t, e);
        }
        return ret;
    };

    function _do_while(cond, body) {
        return when_constant(cond, function(cond, val){
            if (!val) {//while(false){}变成空语句
                warn_unreachable(body);
                return [ "block" ];
            } else {//while(true){}变成for(;;){} 缩短4个字符！
                return [ "for", null, null, null, walk(body) ];
            }
        });
    };

    //遍历AST树 此时遍历名已经混淆过~
    return w.with_walkers({
    	//对于表达式 expr[subscript] 的优化
        "sub": function(expr, subscript) {
            if (subscript[0] == "string") {
                var name = subscript[1];
                if (is_identifier(name))
                	//a["b"] ==> a.b
                	//这样可以省去3个字符
                    return [ "dot", walk(expr), name ];
                else if (/^[1-9][0-9]*$/.test(name) || name === "0")
                	//a[010] => a[8]
                	//表达式可能是八进制的，化成10禁止会更短
                    return [ "sub", walk(expr), [ "num", parseInt(name, 10) ] ];
            }
        },
        "if": make_if,
        "toplevel": function(body) {
            return [ "toplevel", tighten(body) ];
        },
        "switch": function(expr, body) {
            var last = body.length - 1;
            return [ "switch", walk(expr), MAP(body, function(branch, i){
                var block = tighten(branch[1]);
                if (i == last && block.length > 0) {
                	//最后一个case分支，最后一句的break;可以去掉
                	//留意break labelName;这种是不能省略的
                    var node = block[block.length - 1];
                    if (node[0] == "break" && !node[1])
                        block.pop();//忽略最后一句break;
                }
                return [ branch[0] ? walk(branch[0]) : null, block ];
            }) ];
        },
        "function": _lambda,
        "defun": _lambda,
        "block": function(body) {
            if (body) return rmblock([ "block", tighten(body) ]);
        },
        "binary": function(op, left, right) {
            return when_constant([ "binary", op, walk(left), walk(right) ], function yes(c){
                return best_of(walk(c), this);
            }, function no() {
                return function(){
                    if(op != "==" && op != "!=") return;
                    //只有==跟!=才压缩
                    var l = walk(left), r = walk(right);

                    //!1 == right
                    if(l && l[0] == "unary-prefix" && l[1] == "!" && l[2][0] == "num")
                        left = ['num', +!l[2][1]];

                    //left == !2
                    else if (r && r[0] == "unary-prefix" && r[1] == "!" && r[2][0] == "num")
                        right = ['num', +!r[2][1]];

                    return ["binary", op, left, right];
                }() || this;
            });
        },
        "conditional": function(c, t, e) {
            return make_conditional(walk(c), walk(t), walk(e));
        },
        "try": function(t, c, f) {
            return [
                "try",
                tighten(t),
                c != null ? [ c[0], tighten(c[1]) ] : null,
                f != null ? tighten(f) : null
            ];
        },
        "unary-prefix": function(op, expr) {
            expr = walk(expr);
            var ret = [ "unary-prefix", op, expr ];
            if (op == "!")//!(a>=b) 优化成 a<b
                ret = best_of(ret, negate(expr));
            return when_constant(ret, function(ast, val){
                return walk(ast); // it's either true or false, so minifies to !0 or !1
            }, function() { return ret });
        },
        "name": function(name) {
            switch (name) {
              //把true变成!0 
              case "true": return [ "unary-prefix", "!", [ "num", 0 ]];

              //把false变成!1
              case "false": return [ "unary-prefix", "!", [ "num", 1 ]];
            }
        },
        "while": _do_while,
        "assign": function(op, lvalue, rvalue) {
            lvalue = walk(lvalue);
            rvalue = walk(rvalue);
            var okOps = [ '+', '-', '/', '*', '%', '>>', '<<', '>>>', '|', '^', '&' ];
            //赋值语句一般是+= -= ，所以语法分析时候解析出来的op是去掉=的结果，
            //但是如果是a = 1的话,op不好用一个空字符串来表示，所以用了true
            //a = a + b; 优化成为 a += b
            if (op === true && lvalue[0] === "name" && rvalue[0] === "binary" &&
                ~okOps.indexOf(rvalue[1]) && rvalue[2][0] === "name" &&
                rvalue[2][1] === lvalue[1]) {
            	//原本是：["assign", true, ["name", "a"], ["binary", ["name", "a"], ["name", "b"]]]
            	//压缩成：["assign", "+", ["name", "a"], ["name", "b"]]
                return [ this[0], rvalue[1], lvalue, rvalue[3] ]
            }
            return [ this[0], op, lvalue, rvalue ];
        },
        "call": function(expr, args) {
            expr = walk(expr);
            //把"string".toString();替换成"string"
            if (options.unsafe && expr[0] == "dot" && expr[1][0] == "string" && expr[2] == "toString") {
                return expr[1];
            }
            return [ this[0], expr,  MAP(args, walk) ];
        },
        "num": function (num) {
            if (!isFinite(num))//如果是无穷大或者NaN
            	//Infinity => 1/0
            	//-Infinity => -1/0
            	//NaN => 0/0
                return [ "binary", "/", num === 1 / 0
                         ? [ "num", 1 ] : num === -1 / 0
                         ? [ "unary-prefix", "-", [ "num", 1 ] ]
                         : [ "num", 0 ], [ "num", 0 ] ];

            return [ this[0], num ];
        }
    }, function() {
    	//遍历之前先处理一下IF
    	//这里还重复处理两次？@unkowned
        return walk(prepare_ifs(walk(prepare_ifs(ast))));
    });
};

//去除重复的指示性字符串，例如
/*
	function (){
		"use strict";
		function (){
			"use strict";
		}
	}
	压缩成：

	function (){
		"use strict";
		function (){
		}
	}
*/
function squeeze_2(ast, options) {
    var w = ast_walker(), walk = w.walk, scope;
    function with_scope(s, cont) {
        var save = scope, ret;
        scope = s;
        ret = cont();
        scope = save;
        return ret;
    };
    function lambda(name, args, body) {
        return [ this[0], name, args, with_scope(body.scope, curry(MAP, body, walk)) ];
    };
    return w.with_walkers({
        "directive": function(dir) {
            if (scope.active_directive(dir))
                return [ "block" ];
            scope.directives.push(dir);
        },
        "toplevel": function(body) {
            return [ this[0], with_scope(this.scope, curry(MAP, body, walk)) ];
        },
        "function": lambda,
        "defun": lambda
    }, function(){
        return walk(ast_add_scope(ast));
    });
};
