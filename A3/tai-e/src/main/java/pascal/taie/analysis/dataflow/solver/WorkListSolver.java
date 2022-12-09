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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        //TODO - finish me

        Queue<Node> q = new LinkedList<>();
        Set<Node> vis = new HashSet<>();

        for(Node node : cfg){
            if(!cfg.isEntry(node)){
                q.add(node);
                vis.add(node);
            }
        }

        while(!q.isEmpty()){
            Node cur = q.poll();
            vis.remove(cur);

            Fact in = result.getInFact(cur);
            Fact out = result.getOutFact(cur);
            for(Node pred : cfg.getPredsOf(cur)){
                analysis.meetInto(result.getOutFact(pred), in);
            }
            boolean res = analysis.transferNode(cur, in, out);
            if(res){
                for(Node succ : cfg.getSuccsOf(cur)){
                    if(!vis.contains(succ)){
                        q.add(succ);
                        vis.add(succ);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        //TODO - finish me

        Queue<Node> q = new LinkedList<>();
        Set<Node> vis = new HashSet<>();

        for(Node node : cfg){
            if(!cfg.isExit(node)){
                q.add(node);
                vis.add(node);
            }
        }

        while(!q.isEmpty()){
            Node cur = q.poll();
            vis.remove(cur);

            Fact in = result.getInFact(cur);
            Fact out = result.getOutFact(cur);
            for(Node succ : cfg.getSuccsOf(cur)){
                analysis.meetInto(out, result.getInFact(succ));
            }
            boolean res = analysis.transferNode(cur, in, out);
            if(res){
                for(Node succ : cfg.getPredsOf(cur)){
                    if(!vis.contains(succ)){
                        q.add(succ);
                        vis.add(succ);
                    }
                }
            }
        }
    }
}
