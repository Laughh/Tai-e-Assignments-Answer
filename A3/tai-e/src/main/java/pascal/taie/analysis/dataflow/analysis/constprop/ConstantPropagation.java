/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;


public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me

        CPFact res = new CPFact();
        for(Var arg : cfg.getIR().getParams()){
            if(canHoldInt(arg)) {
                res.update(arg, Value.getNAC());
            }
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me

        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me

        fact.entries().forEach(entry -> {
            Var key = entry.getKey();
            Value v = entry.getValue();
            target.update(key, meetValue(target.get(key), v));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me

        if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if(v1.isConstant() && v2.isConstant()){
            if(v1.getConstant() != v2.getConstant()) {
                return Value.getNAC();
            }else {
                return Value.makeConstant(v1.getConstant());
            }
        }else if(v1.isConstant()){
            return Value.makeConstant(v1.getConstant());
        }else{
            return Value.makeConstant(v2.getConstant());
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        // NOTE: 需要使用 canHoldInt 来过滤 stmt 中的 Var

        boolean change = false;

        for(Var key : in.keySet()){
            change |= out.update(key, in.get(key));
        }

        if(stmt instanceof DefinitionStmt<?, ?> def){
            LValue left = def.getLValue();
            if(left instanceof Var x){
                if(canHoldInt(x)){
                    Value res = evaluate(def.getRValue(), in);
                    change |= out.update(x, res);
                }
            }
        }
        return change;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        //TODO - finish me

        if(exp instanceof Var v) {
            return in.get(v);
        }

        if(exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }

        if(!(exp instanceof BinaryExp biExp)) {
            return Value.getNAC();
        }

        String op = ((BinaryExp) exp).getOperator().toString();
        Value valX = in.get(biExp.getOperand1());
        Value valY = in.get(biExp.getOperand2());

        if((op.equals("/") || op.equals("%")) && (valY.isConstant() && valY.getConstant() == 0)){
            return Value.getUndef();
        }

        if(valX.isNAC() || valY.isNAC()) {
            return Value.getNAC();
        }
        if(valX.isUndef() || valY.isUndef()) {
            return Value.getUndef();
        }

        int x = valX.getConstant(), y = valY.getConstant();
        int res;

        res = switch (op){
            case "+" -> x + y;
            case "*" -> x * y;
            case "-" -> x - y;
            case "/" -> x / y;
            case "%" -> x % y;
            case "|" -> x | y;
            case "&" -> x & y;
            case "^" -> x ^ y;
            case "==" -> trans(x == y);
            case "!=" -> trans(x != y);
            case "<" -> trans(x < y);
            case ">" -> trans(x > y);
            case "<=" -> trans(x <= y);
            case ">=" -> trans(x >= y);
            case "<<" -> x << y;
            case ">>" -> x >> y;
            default ->  x >>> y;
        };
        return Value.makeConstant(res);
    }

    private static int trans(boolean res){
        return res ? 1 : 0;
    }
}



