/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2019-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.db;

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.util.IntArrayWrapper;
import edu.harvard.seas.pl.formulog.util.Pair;
import java.lang.reflect.InvocationTargetException;
import java.util.Comparator;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import org.apache.bcel.Const;
import org.apache.bcel.generic.ASTORE;
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

public class TupleComparatorGenerator extends ClassLoader {

  private static final Type objectType = new ObjectType("java.lang.Object");
  private static final Type termType = new ObjectType("edu.harvard.seas.pl.formulog.ast.Term");
  private static final Type termArrayType = new ArrayType(termType, 1);

  private final AtomicInteger cnt = new AtomicInteger();
  private Map<IntArrayWrapper, Comparator<Term[]>> memo = new ConcurrentHashMap<>();

  public Comparator<Term[]> generate(int[] accessPat)
      throws InstantiationException,
          IllegalAccessException,
          IllegalArgumentException,
          InvocationTargetException,
          NoSuchMethodException,
          SecurityException {
    IntArrayWrapper key = new IntArrayWrapper(accessPat);
    Comparator<Term[]> cmp = memo.get(key);
    if (cmp == null) {
      cmp = generate1(accessPat);
      Comparator<Term[]> cmp2 = memo.putIfAbsent(key, cmp);
      if (cmp2 != null) {
        cmp = cmp2;
      }
    }
    return cmp;
  }

  @SuppressWarnings("unchecked")
  public Comparator<Term[]> generate1(int[] accessPat)
      throws InstantiationException,
          IllegalAccessException,
          IllegalArgumentException,
          InvocationTargetException,
          NoSuchMethodException,
          SecurityException {
    String className = "edu.harvard.seas.pl.formulog.db.CustomComparator" + cnt.getAndIncrement();
    ClassGen classGen =
        new ClassGen(
            className,
            "java.lang.Object",
            "",
            Const.ACC_PUBLIC | Const.ACC_SUPER,
            new String[] {"java.util.Comparator"});

    classGen.addEmptyConstructor(Const.ACC_PUBLIC);
    addCompareMethod(classGen, accessPat);

    byte[] data = classGen.getJavaClass().getBytes();
    Class<?> c = defineClass(className, data, 0, data.length);
    return (Comparator<Term[]>) c.getDeclaredConstructor().newInstance();
  }

  private void addCompareMethod(ClassGen cg, int[] accessPat) {
    InstructionFactory f = new InstructionFactory(cg);
    InstructionList il = new InstructionList();
    il.append(genCast(f, 1));
    il.append(genCast(f, 2));
    InstructionHandle ih = null;
    BranchInstruction br = null;
    for (int i : accessPat) {
      Pair<InstructionList, BranchInstruction> p = genComparison(f, i);
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
    MethodGen mg =
        new MethodGen(
            Const.ACC_PUBLIC,
            Type.INT,
            new Type[] {objectType, objectType},
            new String[] {"xs", "ys"},
            "compare",
            cg.getClassName(),
            il,
            cg.getConstantPool());
    mg.setMaxStack();
    mg.setMaxLocals();
    cg.addMethod(mg.getMethod());
  }

  private InstructionList genCast(InstructionFactory f, int argn) {
    assert argn == 1 || argn == 2;
    InstructionList il = new InstructionList();
    il.append(InstructionFactory.createLoad(objectType, argn));
    il.append(f.createCast(objectType, termArrayType));
    il.append(new ASTORE(argn));
    return il;
  }

  private Pair<InstructionList, BranchInstruction> genComparison(InstructionFactory f, int idx) {
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
    il.append(
        f.createInvoke(
            "edu.harvard.seas.pl.formulog.ast.Term",
            "getId",
            Type.INT,
            new Type[] {},
            Const.INVOKEINTERFACE));
    il.append(new ISTORE(argn + 2));
    return il;
  }

  private Pair<InstructionList, BranchInstruction> genICmp(InstructionFactory f, boolean firstCmp) {
    InstructionList il = new InstructionList();
    il.append(new ILOAD(3));
    il.append(new ILOAD(4));
    BranchInstruction br =
        InstructionFactory.createBranchInstruction(
            firstCmp ? Const.IF_ICMPGE : Const.IF_ICMPLE, null);
    il.append(br);
    il.append(new PUSH(f.getConstantPool(), firstCmp ? -1 : 1));
    il.append(InstructionConst.IRETURN);
    return new Pair<>(il, br);
  }
}
