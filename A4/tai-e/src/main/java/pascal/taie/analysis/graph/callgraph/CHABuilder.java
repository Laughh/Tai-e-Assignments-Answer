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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);

        while(!workList.isEmpty()){
            JMethod cur = workList.poll();

            if(callGraph.contains(cur)){
                continue;
            }
            callGraph.addReachableMethod(cur);
            for(Stmt stmt : cur.getIR().getStmts()){
                if(stmt instanceof Invoke callSite){
                    for(JMethod callee : resolve(callSite)){
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
                        workList.add(callee);
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

        Set<JMethod> targets = new HashSet<>();

        MethodRef methodRef = callSite.getMethodRef();
        JClass jClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();

        if(callSite.isVirtual() || callSite.isInterface()){
            Queue<JClass> queue = new LinkedList<>();
            queue.add(jClass);

            while(!queue.isEmpty()){
                JClass cur = queue.poll();

                JMethod res = dispatch(cur, subsignature);
                if(res != null){
                    targets.add(res);
                }
                if(cur.isInterface()){
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(cur));
                    queue.addAll(hierarchy.getDirectImplementorsOf(cur));
                }else{
                    queue.addAll(hierarchy.getDirectSubclassesOf(cur));
                }
            }
        }
        if(callSite.isStatic() || callSite.isSpecial()){
            targets.add(dispatch(jClass, subsignature));
        }

        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jClass, Subsignature subsignature) {
        // TODO - finish me

        if(jClass == null){
            return null;
        }

        JMethod jmethod = jClass.getDeclaredMethod(subsignature);
        if(jmethod != null && !jmethod.isAbstract()){
            return jmethod;
        }
        return dispatch(jClass.getSuperClass(), subsignature);
    }
}
