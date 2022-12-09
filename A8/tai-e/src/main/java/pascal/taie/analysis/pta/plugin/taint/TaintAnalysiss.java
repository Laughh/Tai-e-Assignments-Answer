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

package pascal.taie.analysis.pta.plugin.taint;

import heros.flowfunc.Transfer;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final Set<JMethod> baseToResult;

    private final Set<JMethod> argToBase;

    private final Set<JMethod> argToResult;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        baseToResult = new HashSet<>();
        argToBase = new HashSet<>();
        argToResult = new HashSet<>();

        processTransfer();
    }

    private void processTransfer(){
        for(TaintTransfer transfer : config.getTransfers()){
            JMethod method = transfer.method();
            int from = transfer.from(), to = transfer.to();
            // NOTE: base = -1, result = -2
            if(from == -1 && to == -2) {
                baseToResult.add(method);
            }
            if(from >= 0 && to == -1){
                argToBase.add(method);
            }
            if(from >= 0 && to == -2){
                argToResult.add(method);
            }
        }
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        List<JMethod> methodList = result.getCallGraph().reachableMethods().toList();
        for(JMethod method : methodList){
            for(Stmt stmt : method.getIR()) {
                if(stmt instanceof Invoke invoke){
                    JMethod callee = invoke.getMethodRef().resolve();

                    for(Sink sink : config.getSinks()){
                        if(callee.equals(sink.method())){
                            int index = sink.index();
                             Set<Obj> set =  result.getPointsToSet(invoke.getInvokeExp().getArg(index));
                             for(Obj obj : set){
//                                 System.out.println(invoke + " --> " + obj);
                                 if(isTaint(obj)){
                                     taintFlows.add(new TaintFlow(manager.getSourceCall(obj), invoke, index));
                                 }
                             }
                        }
                    }
                }
            }
        }
        return taintFlows;
    }

    public Obj makeTaint(Invoke invoke, JMethod method){
        for(Source src : config.getSources()){
            if(src.method().equals(method)){
                return manager.makeTaint(invoke, src.type());
            }
        }
        return null;
    }

    public boolean isTaint(Obj obj){
        return manager.isTaint(obj);
    }

    public boolean isBaseToResult(JMethod callee){
        return baseToResult.contains(callee);
    }

    public boolean isArgToBase(JMethod callee){
        return argToBase.contains(callee);
    }

    public boolean isArgToResult(JMethod callee){
        return argToResult.contains(callee);
    }

}
