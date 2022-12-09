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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;
import java.util.stream.Stream;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";
    private final ConstantPropagation cp;
    private final Map<Var, Set<Var>> alias;
    private final Map<JField, Set<LoadField>> staticLoadFields;
    private final Map<JField, Set<StoreField>> staticStoreFields;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        alias = new HashMap<>();
        staticStoreFields = new HashMap<>();
        staticLoadFields = new HashMap<>();
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);

        // NOTE: get alias
        Collection<Var> vars = pta.getVars();
        for (Var x : vars) {
            alias.put(x, new HashSet<>() {{
                add(x);
            }});
            Set<Obj> pointsToSet = pta.getPointsToSet(x);
            for (Var y : vars) {
                if (!x.equals(y)) {
                    for (Obj obj : pta.getPointsToSet(y)){
                        if (pointsToSet.contains(obj)) {
                            alias.get(x).add(y);
                            break;
                        }
                    }
                }
            }
        }
        // NOTE: get static field statement
        for (Stmt stmt : icfg) {
            if (stmt instanceof StoreField storeField) {
                if (storeField.isStatic()) {
                    JField field = storeField.getFieldRef().resolve();
                    if (!staticStoreFields.containsKey(field)) {
                        staticStoreFields.put(field, new HashSet<>());
                    }
                    staticStoreFields.get(field).add(storeField);
                }
            } else if (stmt instanceof LoadField loadField) {
                if (loadField.isStatic()) {
                    JField field = loadField.getFieldRef().resolve();
                    if (!staticLoadFields.containsKey(field)) {
                        staticLoadFields.put(field, new HashSet<>());
                    }
                    staticLoadFields.get(field).add(loadField);
                }
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        boolean change = false;
        for(Var key : in.keySet()){
            change |= out.update(key, in.get(key));
        }
        return change;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        boolean change = false;

        for(Var key : in.keySet()){
            change |= out.update(key, in.get(key));
        }

        // NOTE: x.f = y
        if(stmt instanceof StoreField storeField){
            Var right = storeField.getRValue();
            if(canHoldInt(right)){
                JField field = storeField.getFieldRef().resolve();
                if(storeField.isStatic()){
                    staticLoadFields.getOrDefault(field, new HashSet<>()).forEach(solver::add);
                }else{
                    Var base = ((InstanceFieldAccess) storeField.getLValue()).getBase();
                    for(Var x : alias.getOrDefault(base, new HashSet<>())){
                        x.getLoadFields()
                                .stream()
                                .filter(loadField -> field.equals(loadField.getFieldRef().resolve()))
                                .forEach(solver::add);
                    }
                }
            }
            change = true;
        }else if(stmt instanceof LoadField loadField){    // NOTE: y = x.f
            Var left = loadField.getLValue();
            if(canHoldInt(left)){
                Value res = Value.getUndef();
                JField field = loadField.getFieldRef().resolve();

                if(loadField.isStatic()){
                    for(StoreField storeField : staticStoreFields.getOrDefault(field, new HashSet<>())){
                        CPFact inFact = solver.getInFact(storeField);
                        res = cp.meetValue(res, inFact.get(storeField.getRValue()));
                    }
                }else{
                    Var base = ((InstanceFieldAccess) loadField.getRValue()).getBase();

                    for(Var x : alias.getOrDefault(base, new HashSet<>())){
                        for(StoreField storeField : x.getStoreFields()){
                            if(storeField.getFieldRef().resolve().equals(field)){
                                CPFact inFact = solver.getInFact(storeField);
                                res = cp.meetValue(res, inFact.get(storeField.getRValue()));
                            }
                        }
                    }
                }
                change |= out.update(left, res);
            }
        }else if(stmt instanceof StoreArray storeArray){
            if(canHoldInt(storeArray.getRValue())){
                ArrayAccess access = storeArray.getArrayAccess();

                for(Var x : alias.getOrDefault(access.getBase(), new HashSet<>())){
                    x.getLoadArrays().forEach(solver::add);
                }
            }
            change = true;
        }else if(stmt instanceof LoadArray loadArray){      // NOTE: x = a[i]
            Var left = loadArray.getLValue();
            if(canHoldInt(left)){
                Value res = Value.getUndef();
                ArrayAccess access = loadArray.getArrayAccess();

                for(Var x : alias.getOrDefault(access.getBase(), new HashSet<>())){
                    for(StoreArray storeArray : x.getStoreArrays()){
                        CPFact inFact = solver.getInFact(storeArray);
                        if(checkIndex(in.get(access.getIndex()), inFact.get(storeArray.getArrayAccess().getIndex()))){
                            res = cp.meetValue(res, inFact.get(storeArray.getRValue()));
                        }
                    }
                }
                change |= out.update(left, res);
            }
        }else if(stmt instanceof DefinitionStmt<?, ?> def){
            LValue left = def.getLValue();
            if(left instanceof Var x){
                if(canHoldInt(x)){
                    Value res = ConstantPropagation.evaluate(def.getRValue(), in);
                    change |= out.update(x, res);
                }
            }
        }
        return change;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        return out.copy();
    }

        @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me

        CPFact ret = out.copy();
        LValue L = edge.getSource().getDef().orElse(null);
        if(L instanceof Var x){
            ret.remove(x);
        }
        return ret;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me

        CPFact ret = new CPFact();

        List<Var> formal = edge.getCallee().getIR().getParams();
        List<Var> args = ((Invoke) edge.getSource()).getInvokeExp().getArgs();

        for(int i = 0; i < formal.size(); ++i){
            Var x = formal.get(i);
            if(canHoldInt(x)){
                ret.update(x, callSiteOut.get(args.get(i)));
            }
        }
        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me

        CPFact ret = new CPFact();
        LValue L = edge.getCallSite().getDef().orElse(null);

        if(L instanceof Var def && canHoldInt(def)){
            for(Var x : edge.getReturnVars()){
                ret.update(def, cp.meetValue(ret.get(def), returnOut.get(x)));
            }
        }
        return ret;
    }

    private boolean checkIndex(Value x, Value y){
        if(x.isUndef() || y.isUndef()){
            return false;
        }
        if(x.isConstant() && y.isConstant()){
            return x.equals(y);
        }
        return true;
    }
}
