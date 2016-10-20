/*
 * FindBugs - Find Bugs in Java programs
 * Copyright (C) 2003-2008 University of Maryland
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package edu.umd.cs.findbugs.detect;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.bcel.Const;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MULTIANEWARRAY;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.POP;
import org.apache.bcel.generic.POP2;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.generic.Type;

import edu.umd.cs.findbugs.BugInstance;
import edu.umd.cs.findbugs.BugReporter;
import edu.umd.cs.findbugs.Detector;
import edu.umd.cs.findbugs.StringAnnotation;
import edu.umd.cs.findbugs.ba.AnalysisContext;
import edu.umd.cs.findbugs.ba.BasicBlock;
import edu.umd.cs.findbugs.ba.CFG;
import edu.umd.cs.findbugs.ba.ClassContext;
import edu.umd.cs.findbugs.ba.DataflowAnalysisException;
import edu.umd.cs.findbugs.ba.EdgeTypes;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.ba.XClass;
import edu.umd.cs.findbugs.ba.XMethod;
import edu.umd.cs.findbugs.ba.type.TypeAnalysis;
import edu.umd.cs.findbugs.ba.type.TypeFrame;
import edu.umd.cs.findbugs.ba.vna.ValueNumber;
import edu.umd.cs.findbugs.ba.vna.ValueNumberAnalysis;
import edu.umd.cs.findbugs.ba.vna.ValueNumberFrame;
import edu.umd.cs.findbugs.classfile.CheckedAnalysisException;
import edu.umd.cs.findbugs.classfile.DescriptorFactory;
import edu.umd.cs.findbugs.classfile.Global;
import edu.umd.cs.findbugs.classfile.MethodDescriptor;
import edu.umd.cs.findbugs.detect.FindNoSideEffectMethods.MethodSideEffectStatus;
import edu.umd.cs.findbugs.detect.FindNoSideEffectMethods.NoSideEffectMethodsDatabase;

/**
 * @author Tagir Valeev
 */
public class FindUselessObjects implements Detector {
    private static final int MAX_ITERATIONS = 50;
    private final BugReporter reporter;
    private final NoSideEffectMethodsDatabase noSideEffectMethods;

    private static class ValueInfo {
        Location created;
        String var;
        int origValue;
        boolean hasObjectOnlyCall;
        boolean escaped;
        boolean used;
        boolean derivedEscaped;
        public BitSet origValues;
        public BitSet derivedValues = new BitSet();
        Type type;

        public ValueInfo(int origValue, Location location, Type type) {
            this.created = location;
            this.origValue = origValue;
            this.type = type;
        }

        @Override
        public String toString() {
            return "[" + (escaped ? "E" : "-") + (hasObjectOnlyCall ? "O" : "-") + (used ? "U" : "-")
                    + (derivedEscaped ? "D" : "-") + "] " + (var == null ? "" : var + " ") + type + " " + created;
        }
    }

    private class UselessValuesContext {
        ValueNumberAnalysis vna;
        TypeAnalysis ta;
        CFG cfg;
        int count;
        Map<Integer, ValueInfo> observedValues = new HashMap<>();
        ConstantPoolGen cpg;
        Map<Integer, Set<ValueInfo>> values;
        ValueNumber thisValue;
        ClassContext classContext;
        Method method;

        UselessValuesContext(ClassContext classContext, Method method) throws CheckedAnalysisException {
            this.classContext = classContext;
            this.method = method;
            cfg = classContext.getCFG(method);
            cpg = cfg.getMethodGen().getConstantPool();
            ta = classContext.getTypeDataflow(method).getAnalysis();
            vna = classContext.getValueNumberDataflow(method).getAnalysis();
        }

        void initObservedValues() throws DataflowAnalysisException {
            for(Iterator<Location> iterator = cfg.locationIterator(); iterator.hasNext(); ) {
                Location location = iterator.next();
                Instruction instruction = location.getHandle().getInstruction();
                if(instruction instanceof ANEWARRAY || instruction instanceof NEWARRAY || instruction instanceof MULTIANEWARRAY) {
                    int number = vna.getFactAfterLocation(location).getTopValue().getNumber();
                    TypeFrame typeFrame = ta.getFactAfterLocation(location);
                    if(typeFrame.isValid()) {
                        Type type = typeFrame.getTopValue();
                        observedValues.put(number, new ValueInfo(number, location, type));
                    }
                } else if(instruction instanceof INVOKESPECIAL) {
                    InvokeInstruction inv = (InvokeInstruction) instruction;
                    if (inv.getMethodName(cpg).equals("<init>")
                            && noSideEffectMethods.hasNoSideEffect(new MethodDescriptor(inv, cpg))) {
                        int number = vna.getFactAtLocation(location).getStackValue(inv.consumeStack(cpg)-1).getNumber();
                        TypeFrame typeFrame = ta.getFactAtLocation(location);
                        if(typeFrame.isValid()) {
                            Type type = typeFrame.getStackValue(inv.consumeStack(cpg)-1);
                            observedValues.put(number, new ValueInfo(number, location, type));
                        }
                    }
                }
            }
            thisValue = vna.getThisValue();
            if(thisValue != null) {
                observedValues.remove(thisValue.getNumber());
            }
            count = observedValues.size();
        }

        void enhanceViaMergeTree() {
            values = new HashMap<>();
            for (Entry<Integer, ValueInfo> entry : observedValues.entrySet()) {
                BitSet outputSet = vna.getMergeTree().getTransitiveOutputSet(entry.getKey());
                outputSet.set(entry.getKey());
                entry.getValue().origValues = outputSet;
                for (int i = outputSet.nextSetBit(0); i >= 0; i = outputSet.nextSetBit(i+1)) {
                    Set<ValueInfo> list = values.get(i);
                    if(list == null) {
                        list = new HashSet<>();
                        values.put(i, list);
                    }
                    list.add(entry.getValue());
                }
            }
        }

        boolean setEscape(Set<ValueInfo> vals) {
            boolean result = false;
            for(ValueInfo vi : vals) {
                result |= !vi.escaped;
                vi.escaped = true;
                count--;
            }
            return result;
        }

        boolean setDerivedEscape(Set<ValueInfo> vals, ValueNumber vn) {
            boolean result = false;
            for(ValueInfo vi : vals) {
                if(vi.origValues.get(vn.getNumber())) {
                    result |= !vi.derivedEscaped;
                    vi.derivedEscaped = true;
                }
            }
            return result;
        }

        boolean setUsed(Set<ValueInfo> vals) {
            boolean result = false;
            for(ValueInfo vi : vals) {
                result |= !vi.used;
                vi.used = true;
            }
            return result;
        }

        boolean setObjectOnly(Set<ValueInfo> vals, ValueNumber vn) {
            boolean result = false;
            for(ValueInfo vi : vals) {
                if(vi.origValues.get(vn.getNumber()) || (!vi.derivedEscaped && vi.derivedValues.get(vn.getNumber()))) {
                    result |= !vi.hasObjectOnlyCall;
                    vi.hasObjectOnlyCall = true;
                } else {
                    result |= !vi.escaped;
                    vi.escaped = true;
                    count--;
                }
            }
            return result;
        }

        boolean propagateValues(Set<ValueInfo> vals, ValueNumber origNumber, ValueNumber vn) {
            int number = vn.getNumber();
            if(vals.size() == 1 && vals.iterator().next().origValue == number) {
                return false;
            }
            boolean result = setUsed(vals);
            if(origNumber != null) {
                for(ValueInfo vi : vals) {
                    if(vi.origValues.get(origNumber.getNumber()) && !vi.derivedValues.get(number)) {
                        vi.derivedValues.set(number);
                        result = true;
                    }
                }
            }
            Set<ValueInfo> list = values.get(number);
            if(list == null) {
                list = new HashSet<>();
                values.put(number, list);
            }
            result |= list.addAll(vals);
            BitSet outputSet = vna.getMergeTree().getTransitiveOutputSet(number);
            for (int i = outputSet.nextSetBit(0); i >= 0; i = outputSet.nextSetBit(i+1)) {
                list = values.get(i);
                if(list == null) {
                    list = new HashSet<>();
                    values.put(i, list);
                }
                result |= list.addAll(vals);
            }
            return result;
        }

        boolean propagateToReturnValue(Set<ValueInfo> vals, ValueNumber vn, GenLocation location, MethodDescriptor m)
                throws DataflowAnalysisException {
            for(ValueInfo vi : vals) {
                if(vi.type.getSignature().startsWith("[") && vi.hasObjectOnlyCall && vi.var == null && vn.getNumber() == vi.origValue) {
                    // Ignore initialized arrays passed to methods
                    vi.escaped = true;
                    count--;
                }
            }
            if (Type.getReturnType(m.getSignature()) == Type.VOID || location instanceof ExceptionLocation) {
                return false;
            }
            InstructionHandle nextHandle = location.getHandle().getNext();
            if (nextHandle == null || (nextHandle.getInstruction() instanceof POP || nextHandle.getInstruction() instanceof POP2)) {
                return false;
            }
            return propagateValues(vals, null, location.frameAfter().getTopValue());
        }

        boolean isEmpty() {
            return count == 0;
        }

        Iterator<GenLocation> genIterator() {
            return new Iterator<FindUselessObjects.GenLocation>() {
                Iterator<Location> locIterator = cfg.locationIterator();
                Iterator<BasicBlock> blockIterator = cfg.blockIterator();
                GenLocation next = advance();

                private GenLocation advance() {
                    if(locIterator.hasNext()) {
                        return new RegularLocation(ta, vna, locIterator.next());
                    }
                    while(blockIterator.hasNext()) {
                        BasicBlock block = blockIterator.next();
                        if(block.isExceptionThrower() && cfg.getOutgoingEdgeWithType(block, EdgeTypes.FALL_THROUGH_EDGE) == null) {
                            return new ExceptionLocation(ta, vna, block);
                        }
                    }
                    return null;
                }

                @Override
                public boolean hasNext() {
                    return next != null;
                }

                @Override
                public GenLocation next() {
                    if (!hasNext()) {
                        throw new NoSuchElementException();
                    }
                    GenLocation cur = next;
                    next = advance();
                    return cur;
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }
            };
        }

        boolean escaped(ValueNumber vn) {
            Set<ValueInfo> vals = values.get(vn.getNumber());
            if(vals == null) {
                return true;
            }
            for(ValueInfo vi : vals) {
                if(vi.escaped) {
                    return true;
                }
            }
            return false;
        }

        Set<ValueInfo> getLiveVals(ValueNumber vn) {
            Set<ValueInfo> vals = this.values.get(vn.getNumber());
            if(vals == null) {
                return null;
            }
            if(vals.size() == 1) {
                return vals.iterator().next().escaped ? null : vals;
            }
            Set<ValueInfo> result = new HashSet<>();
            for(ValueInfo vi : vals) {
                if(!vi.escaped) {
                    result.add(vi);
                }
            }
            return result.isEmpty() ? null : result;
        }

        void report() {
            for(ValueInfo vi : observedValues.values()) {
                if(!vi.escaped) {
                    if(vi.hasObjectOnlyCall && vi.used && vi.var == null) {
                        continue;
                    }
                    if(vi.hasObjectOnlyCall || (vi.used && vi.var != null)) {
                        BugInstance bug = new BugInstance(vi.var == null ? "UC_USELESS_OBJECT_STACK" : "UC_USELESS_OBJECT",
                                NORMAL_PRIORITY).addClassAndMethod(classContext.getJavaClass(), method);
                        if(vi.var != null) {
                            bug.add(new StringAnnotation(vi.var));
                        }
                        reporter.reportBug(bug.addType(vi.type).addSourceLine(classContext, method, vi.created));
                    }
                }
            }
        }
    }

    private static interface GenLocation {
        InstructionHandle getHandle();
        TypeFrame typeFrameBefore() throws DataflowAnalysisException;
        ValueNumberFrame frameBefore();
        ValueNumberFrame frameAfter();
    }

    private static class RegularLocation implements GenLocation {
        Location loc;
        ValueNumberAnalysis vna;
        TypeAnalysis ta;

        public RegularLocation(TypeAnalysis ta, ValueNumberAnalysis vna, Location loc) {
            this.ta = ta;
            this.vna = vna;
            this.loc = loc;
        }

        @Override
        public InstructionHandle getHandle() {
            return loc.getHandle();
        }

        @Override
        public ValueNumberFrame frameBefore() {
            return vna.getFactAtLocation(loc);
        }

        @Override
        public ValueNumberFrame frameAfter() {
            return vna.getFactAfterLocation(loc);
        }

        @Override
        public TypeFrame typeFrameBefore() throws DataflowAnalysisException {
            return ta.getFactAtLocation(loc);
        }

        @Override
        public String toString() {
            return loc.toString();
        }
    }

    private static class ExceptionLocation implements GenLocation {
        BasicBlock b;
        ValueNumberAnalysis vna;
        TypeAnalysis ta;

        public ExceptionLocation(TypeAnalysis ta, ValueNumberAnalysis vna, BasicBlock block) {
            this.vna = vna;
            this.ta = ta;
            this.b = block;
        }

        @Override
        public InstructionHandle getHandle() {
            return b.getExceptionThrower();
        }

        @Override
        public ValueNumberFrame frameBefore() {
            return vna.getStartFact(b);
        }

        @Override
        public ValueNumberFrame frameAfter() {
            return vna.getResultFact(b);
        }

        @Override
        public TypeFrame typeFrameBefore() {
            return ta.getStartFact(b);
        }

        @Override
        public String toString() {
            return "ex: "+b.getExceptionThrower()+" at "+b;
        }
    }

    public FindUselessObjects(BugReporter reporter) {
        this.reporter = reporter;
        this.noSideEffectMethods = Global.getAnalysisCache().getDatabase(NoSideEffectMethodsDatabase.class);
    }

    @Override
    public void visitClassContext(ClassContext classContext) {
        for(Method method : classContext.getMethodsInCallOrder()) {
            if(method.isAbstract() || method.isNative()) {
                continue;
            }
            try {
                analyzeMethod(classContext, method);
            } catch (CheckedAnalysisException e) {
                reporter.logError("Error analyzing "+method+" (class: "+classContext.getJavaClass().getClassName()+")", e);
            }
        }
    }

    private void analyzeMethod(ClassContext classContext, Method method) throws CheckedAnalysisException {
        LocalVariableTable lvt = method.getLocalVariableTable();
        UselessValuesContext context = new UselessValuesContext(classContext, method);
        context.initObservedValues();
        if(context.isEmpty()) {
            return;
        }
        context.enhanceViaMergeTree();
        boolean changed;
        int iteration = 0;
        do {
            changed = false;
            if(++iteration > MAX_ITERATIONS) {
                AnalysisContext.logError("FindUselessObjects: " + classContext.getClassDescriptor().getDottedClassName() + "."
                        + method.getName() + method.getSignature() + ": cannot converge after " + MAX_ITERATIONS
                        + " iterations; method is skipped");
                return;
            }
            for(Iterator<GenLocation> iterator = context.genIterator(); iterator.hasNext() && !context.isEmpty(); ) {
                GenLocation location = iterator.next();
                Instruction inst = location.getHandle().getInstruction();
                ValueNumberFrame before = location.frameBefore();
                if (!before.isValid()) {
                    continue;
                }
                if(inst instanceof IINC) {
                    int index = ((IINC)inst).getIndex();
                    Set<ValueInfo> vals = context.getLiveVals(before.getValue(index));
                    if(vals != null) {
                        changed |= context.propagateValues(vals, null, location.frameAfter().getValue(index));
                    }
                    continue;
                }
                int nconsumed = inst.consumeStack(context.cpg);
                if(nconsumed > 0) {
                    ValueNumber[] vns = new ValueNumber[nconsumed];
                    before.getTopStackWords(vns);
                    for(int i=0; i<nconsumed; i++) {
                        ValueNumber vn = vns[i];
                        Set<ValueInfo> vals = context.getLiveVals(vn);
                        if(vals != null) {
                            switch(inst.getOpcode()) {
                            case Const.ASTORE:
                            case Const.ASTORE_0:
                            case Const.ASTORE_1:
                            case Const.ASTORE_2:
                            case Const.ASTORE_3:
                                for(ValueInfo vi : vals) {
                                    if(vi.var == null && vi.origValue == vn.getNumber()) {
                                        int index = ((StoreInstruction)inst).getIndex();
                                        LocalVariable lv = lvt == null ? null : lvt.getLocalVariable(index, location.getHandle().getNext().getPosition());
                                        vi.var = lv == null ? "var$"+index : lv.getName();
                                        vi.hasObjectOnlyCall = false;
                                        changed = true;
                                    }
                                }
                                break;
                            case Const.POP:
                            case Const.POP2:
                            case Const.DUP:
                            case Const.DUP2:
                            case Const.DUP_X1:
                            case Const.DUP2_X1:
                            case Const.ISTORE:
                            case Const.ISTORE_0:
                            case Const.ISTORE_1:
                            case Const.ISTORE_2:
                            case Const.ISTORE_3:
                            case Const.LSTORE:
                            case Const.LSTORE_0:
                            case Const.LSTORE_1:
                            case Const.LSTORE_2:
                            case Const.LSTORE_3:
                            case Const.FSTORE:
                            case Const.FSTORE_0:
                            case Const.FSTORE_1:
                            case Const.FSTORE_2:
                            case Const.FSTORE_3:
                            case Const.DSTORE:
                            case Const.DSTORE_0:
                            case Const.DSTORE_1:
                            case Const.DSTORE_2:
                            case Const.DSTORE_3:
                            case Const.SWAP:
                            case Const.IMPDEP1:
                            case Const.IMPDEP2:
                            case Const.CHECKCAST:
                            case Const.MONITORENTER:
                                break;
                            case Const.IADD:
                            case Const.LADD:
                            case Const.FADD:
                            case Const.DADD:
                            case Const.ISUB:
                            case Const.LSUB:
                            case Const.FSUB:
                            case Const.DSUB:
                            case Const.IMUL:
                            case Const.DMUL:
                            case Const.LMUL:
                            case Const.FMUL:
                            case Const.IDIV:
                            case Const.DDIV:
                            case Const.LDIV:
                            case Const.FDIV:
                            case Const.INEG:
                            case Const.LNEG:
                            case Const.FNEG:
                            case Const.DNEG:
                            case Const.IREM:
                            case Const.LREM:
                            case Const.FREM:
                            case Const.DREM:
                            case Const.ISHL:
                            case Const.LSHL:
                            case Const.ISHR:
                            case Const.LSHR:
                            case Const.IUSHR:
                            case Const.LUSHR:
                            case Const.IAND:
                            case Const.LAND:
                            case Const.IOR:
                            case Const.LOR:
                            case Const.IXOR:
                            case Const.LXOR:
                            case Const.I2L:
                            case Const.I2F:
                            case Const.I2D:
                            case Const.L2I:
                            case Const.L2F:
                            case Const.L2D:
                            case Const.F2I:
                            case Const.F2L:
                            case Const.F2D:
                            case Const.D2I:
                            case Const.D2L:
                            case Const.D2F:
                            case Const.I2B:
                            case Const.I2C:
                            case Const.I2S:
                            case Const.LCMP:
                            case Const.FCMPL:
                            case Const.FCMPG:
                            case Const.DCMPL:
                            case Const.DCMPG:
                            case Const.ARRAYLENGTH:
                                changed |= context.propagateValues(vals, null, location.frameAfter().getTopValue());
                                break;
                            case Const.GETFIELD:
                            case Const.AALOAD:
                            case Const.DALOAD:
                            case Const.BALOAD:
                            case Const.CALOAD:
                            case Const.LALOAD:
                            case Const.SALOAD:
                            case Const.IALOAD:
                                changed |= context.propagateValues(vals, vn, location.frameAfter().getTopValue());
                                break;
                            case Const.AASTORE:
                            case Const.DASTORE:
                            case Const.BASTORE:
                            case Const.CASTORE:
                            case Const.LASTORE:
                            case Const.SASTORE:
                            case Const.IASTORE:
                            case Const.PUTFIELD:
                                if(i == 0) {
                                    ValueNumber value = vns[vns.length-1];
                                    if(!value.hasFlag(ValueNumber.CONSTANT_VALUE) && !value.hasFlag(ValueNumber.CONSTANT_CLASS_OBJECT) &&
                                            !context.observedValues.containsKey(value.getNumber())) {
                                        changed |= context.setDerivedEscape(vals, vn);
                                    }
                                    changed |= context.setObjectOnly(vals, vn);
                                } else {
                                    if(context.escaped(vns[0])) {
                                        changed |= context.setEscape(vals);
                                    } else {
                                        changed |= context.propagateValues(vals, null, vns[0]);
                                    }
                                }
                                break;
                            case Const.INVOKESTATIC:
                            case Const.INVOKESPECIAL:
                            case Const.INVOKEINTERFACE:
                            case Const.INVOKEVIRTUAL:
                                MethodDescriptor m = new MethodDescriptor((InvokeInstruction) inst, context.cpg);
                                XMethod xMethod = null;
                                try {
                                    Type type = location.typeFrameBefore().getStackValue(nconsumed-1);
                                    xMethod = Global
                                            .getAnalysisCache()
                                            .getClassAnalysis(XClass.class,
                                                    DescriptorFactory.createClassDescriptorFromSignature(type.getSignature()))
                                                    .findMatchingMethod(m);
                                } catch (CheckedAnalysisException e) {
                                    // ignore
                                }
                                if(xMethod != null) {
                                    m = xMethod.getMethodDescriptor();
                                }
                                MethodSideEffectStatus status = noSideEffectMethods.status(m);
                                if(status == MethodSideEffectStatus.NSE || status == MethodSideEffectStatus.SE_CLINIT) {
                                    if(m.getName().equals("<init>")) {
                                        if(vns[0].equals(context.thisValue)) {
                                            changed |= context.setEscape(vals);
                                        } else {
                                            changed |= context.propagateValues(vals, null, vns[0]);
                                        }
                                    } else {
                                        changed |= context.propagateToReturnValue(vals, vn, location, m);
                                    }
                                    break;
                                }
                                if(status == MethodSideEffectStatus.OBJ) {
                                    if(i == 0) {
                                        changed |= context.setDerivedEscape(vals, vn);
                                        changed |= context.propagateToReturnValue(vals, vn, location, m);
                                        changed |= context.setObjectOnly(vals, vn);
                                        break;
                                    } else {
                                        if(!context.escaped(vns[0])) {
                                            changed |= context.propagateValues(vals, null, vns[0]);
                                            changed |= context.propagateToReturnValue(vals, vn, location, m);
                                            break;
                                        }
                                    }
                                }
                                changed |= context.setEscape(vals);
                                break;
                            default:
                                changed |= context.setEscape(vals);
                                break;
                            }
                        }
                    }
                }
            }
        } while(changed);
        context.report();
    }

    @Override
    public void report() {
    }

}
