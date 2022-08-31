package edu.harvard.seas.pl.formulog.codegen.ast.cpp;

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


import java.io.PrintWriter;

public class CppNewArray implements CppExpr {

    private final String type;
    private final CppExpr size;

    private CppNewArray(String type, CppExpr size) {
        this.type = type;
        this.size = size;
    }

    public static CppNewArray mk(String type, CppExpr size) {
        return new CppNewArray(type, size);
    }

    @Override
    public void print(PrintWriter out) {
        out.print("new ");
        out.print(type);
        out.print("[");
        size.print(out);
        out.print("]");
    }

}
