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

package pascal.taie.analysis.dataflow.inter;

import fj.P;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.stmt.Stmt;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }


    private void initialize() {
        // TODO - finish me
        workList = new LinkedList<>();

        Set<Node> entries = new HashSet<>();

        for (Method method : icfg.entryMethods().toList()) {
            Node entry = icfg.getEntryOf(method);
            if (icfg.getInDegreeOf(entry) == 0) {
                entries.add(entry);
            }
        }

        for (Node node : icfg) {
            if (entries.contains(node)) {
                result.setInFact(node, analysis.newBoundaryFact(node));
            } else {
                result.setInFact(node, analysis.newInitialFact());
            }
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        // TODO - finish me

        workList.addAll(icfg.getNodes());

        while (!workList.isEmpty()) {
            Node cur = workList.poll();

            Fact in = result.getInFact(cur);
            Fact out = result.getOutFact(cur);

            for (ICFGEdge<Node> edge : icfg.getInEdgesOf(cur)) {
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), in);
            }
            boolean change = analysis.transferNode(cur, in, out);
//            System.out.println(cur + ": " + in + " -> " + out);
            if (change) {
                workList.addAll(icfg.getSuccsOf(cur));
            }
        }
    }

    public Fact getInFact(Node node){
        return result.getInFact(node);
    }

    public void add(Node node){
        this.workList.add(node);
    }
}