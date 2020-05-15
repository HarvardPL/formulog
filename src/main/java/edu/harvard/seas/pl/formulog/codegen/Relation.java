package edu.harvard.seas.pl.formulog.codegen;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
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


import java.util.List;

import edu.harvard.seas.pl.formulog.ast.BindingType;

public interface Relation extends CppExpr {

	CppStmt mkDecl();

	CppExpr mkContains(CppExpr expr, boolean useHints);
	
	CppExpr mkContains(int idx, CppExpr expr, boolean useHints);
	
	CppExpr mkInsert(CppExpr expr, boolean useHints);
	
	CppExpr mkInsertAll(CppExpr expr);
	
	CppExpr mkIsEmpty();
	
	CppStmt mkDeclTuple(String name);
	
	CppStmt mkDeclTuple(String name, List<CppExpr> exprs);
	
	CppExpr mkTuple(List<CppExpr> exprs);
	
	CppExpr mkTupleAccess(CppExpr tup, CppExpr idx);
	
	CppStmt mkPrint();
	
	CppExpr mkPartition();
	
	CppStmt mkPurge();
	
	CppExpr mkLookup(int idx, BindingType[] pat, CppExpr key, boolean useHints);
	
	CppExpr mkSize();
	
	RelationStruct getStruct();
	
	CppStmt mkDeclContext();
	
}
