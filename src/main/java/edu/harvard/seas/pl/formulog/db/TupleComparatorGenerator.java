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
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

import edu.harvard.seas.pl.formulog.ast.Term;

public class TupleComparatorGenerator extends ClassLoader {

	private final AtomicInteger cnt = new AtomicInteger();

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

	private void addCompareMethod(ClassGen classGen, int[] accessPat) {
		ConstantPoolGen cp = classGen.getConstantPool();
		InstructionList il = new InstructionList();
	}

}
