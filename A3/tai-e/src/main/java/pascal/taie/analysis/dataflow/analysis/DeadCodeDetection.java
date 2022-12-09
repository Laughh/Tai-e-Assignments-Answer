
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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);

        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // TODO - finish me

        Set<Stmt> vis = new HashSet<>();
        Queue<Stmt> q = new LinkedList<>();

        q.add(cfg.getEntry());
        vis.add(cfg.getEntry());

        while(!q.isEmpty()){
            Stmt cur = q.poll();

            if(cur instanceof If ifStmt){
                CPFact in = constants.getInFact(cur);
                Value res = ConstantPropagation.evaluate(ifStmt.getCondition(), in);
                if(res.isConstant()){
                    Edge.Kind need = res.getConstant() == 0 ? Edge.Kind.IF_FALSE : Edge.Kind.IF_TRUE;

                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(cur)){
                        if(edge.getKind() == need){
                            insert(vis, q, edge.getTarget());
                            break;
                        }
                    }
                    continue;
                }
            }else if(cur instanceof SwitchStmt switchStmt){
                CPFact in = constants.getInFact(cur);
                Value res = ConstantPropagation.evaluate(switchStmt.getVar(), in);

                if(res.isConstant()){
                    boolean gone = false;
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(cur)){
                        if(edge.getKind() == Edge.Kind.SWITCH_CASE && res.getConstant() == edge.getCaseValue()){
                            gone = true;
                            insert(vis, q, edge.getTarget());
                            break;
                        }
                    }
                    if(!gone){
                        insert(vis, q, switchStmt.getDefaultTarget());
                    }
                    continue;
                }
            }else if(cur instanceof AssignStmt<?,?> assign){
                if(assign.getLValue() instanceof Var L) {
                    if (hasNoSideEffect(assign.getRValue()) && !liveVars.getOutFact(cur).contains(L)) {
                        deadCode.add(cur);
                    }
                }
            }

            for(Stmt succ : cfg.getSuccsOf(cur)){
                insert(vis, q, succ);
            }
        }

        for(Stmt node : cfg){
            if(!vis.contains(node)){
                deadCode.add(node);
            }
        }

        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    private void insert(Set<Stmt> vis, Queue<Stmt> q, Stmt node){
        if(!vis.contains(node)){
            q.add(node);
            vis.add(node);
        }
    }
    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}


