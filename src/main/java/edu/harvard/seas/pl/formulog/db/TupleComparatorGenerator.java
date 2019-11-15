package edu.harvard.seas.pl.formulog.db;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import java.util.Comparator;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.bcel.Const;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ILOAD;
import org.apache.bcel.generic.ISTORE;
import org.apache.bcel.generic.InstructionConst;
import org.apache.bcel.generic.InstructionFactory;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.PUSH;
import org.apache.bcel.generic.Type;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.util.Pair;

public class TupleComparatorGenerator extends ClassLoader {

	private static final AtomicInteger cnt = new AtomicInteger();
	
	private static final Type termType = new ObjectType("edu.harvard.seas.pl.formulog.ast.Term");
	private static final Type termArrayType = new ArrayType(termType, 1);

	@SuppressWarnings("unchecked")
	public Comparator<Term[]> generate(int[] accessPat) throws InstantiationException, IllegalAccessException {
		String className = "edu.harvard.seas.pl.formulog.db.CustomComparator" + cnt.getAndIncrement();
		ClassGen classGen = new ClassGen(className, "java.lang.Object", "", Const.ACC_PUBLIC | Const.ACC_SUPER,
				new String[] { "java.util.Comparator" });

		classGen.addEmptyConstructor(Const.ACC_PUBLIC);
		addCompareMethod(classGen, accessPat);

		byte[] data = classGen.getJavaClass().getBytes();
		Class<?> c = defineClass(className, data, 0, data.length);
		return (Comparator<Term[]>) c.newInstance();
	}

	private void addCompareMethod(ClassGen cg, int[] accessPat) {
		InstructionList il = new InstructionList();
		InstructionHandle ih = null;
		BranchInstruction br = null;
		for (int i : accessPat) {
			Pair<InstructionList, BranchInstruction> p = genComparison(cg, i);
			ih = il.append(p.fst());
			if (br != null) {
				br.setTarget(ih);
			}
			br = p.snd();
		}
		ih = il.append(new PUSH(cg.getConstantPool(), 0));
		if (br != null) {
			br.setTarget(ih);
		}
		il.append(InstructionConst.IRETURN);
		MethodGen mg = new MethodGen(Const.ACC_PUBLIC, Type.INT, new Type[] { termArrayType, termArrayType },
				new String[] { "xs", "ys" }, "compare", cg.getClassName(), il, cg.getConstantPool());
		mg.setMaxStack();
		mg.setMaxLocals();
		cg.addMethod(mg.getMethod());
	}

	private Pair<InstructionList, BranchInstruction> genComparison(ClassGen cg, int idx) {
		InstructionFactory f = new InstructionFactory(cg);
		InstructionList il = new InstructionList();
		il.append(genLoad(f, 1, idx));
		il.append(genLoad(f, 2, idx));
		Pair<InstructionList, BranchInstruction> p = genICmp(f, true);
		il.append(p.fst());
		BranchInstruction br = p.snd();
		p = genICmp(f, false);
		br.setTarget(il.append(p.fst()));
		return new Pair<>(il, p.snd());
	}
	
	private InstructionList genLoad(InstructionFactory f, int argn, int idx) {
		assert argn == 1 || argn == 2;
		InstructionList il = new InstructionList();
		il.append(argn == 1 ? InstructionConst.ALOAD_1 : InstructionConst.ALOAD_2);
		il.append(new PUSH(f.getConstantPool(), idx));
		il.append(InstructionConst.AALOAD);
		il.append(f.createInvoke("edu.harvard.seas.pl.formulog.ast.Term", "getId", Type.INT, new Type[] {},
				Const.INVOKEINTERFACE));
		il.append(new ISTORE(argn + 2));
		return il; 
	}
	
	private Pair<InstructionList, BranchInstruction> genICmp(InstructionFactory f, boolean firstCmp) {
		InstructionList il = new InstructionList();
		il.append(new ILOAD(3));
		il.append(new ILOAD(4));
		BranchInstruction br = InstructionFactory.createBranchInstruction(firstCmp ? Const.IF_ICMPGE : Const.IF_ICMPLE, null);
		il.append(br);
		il.append(new PUSH(f.getConstantPool(), firstCmp ? -1 : 1));
		il.append(InstructionConst.IRETURN);
		return new Pair<>(il, br);
	}
	
	public static void main(String[] args) throws InstantiationException, IllegalAccessException {
		TupleComparatorGenerator gen = new TupleComparatorGenerator();
		gen.generate(new int[] { 0 });
	}
	
	/*
	     0: aload_1
         1: iconst_0
         2: aaload
         3: invokeinterface #18,  1           // InterfaceMethod edu/harvard/seas/pl/formulog/ast/Term.getId:()I
         8: istore_3
         9: aload_2
        10: iconst_0
        11: aaload
        12: invokeinterface #18,  1           // InterfaceMethod edu/harvard/seas/pl/formulog/ast/Term.getId:()I
        17: istore        4
        19: iload_3
        20: iload         4
        22: if_icmpge     27
        25: iconst_m1
        26: ireturn
        27: iload_3
        28: iload         4
        30: if_icmple     35
        33: iconst_1
        34: ireturn

	 */

}
