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

public class CppConst<T> implements CppExpr {

    private final T val;

    private CppConst(T val) {
        this.val = val;
    }

    public static CppConst<Boolean> mkTrue() {
        return new CppConst<>(true);
    }

    public static CppConst<Boolean> mkFalse() {
        return new CppConst<>(false);
    }

    public static CppConst<Integer> mkInt(int i) {
        return new CppConst<>(i);
    }

    public static CppConst<String> mkString(String s) {
        return new CppConst<>(s);
    }

    @Override
    public void print(PrintWriter out) {
        boolean isString = val instanceof String;
        if (isString) {
            out.print("\"");
        }
        out.print(val);
        if (isString) {
            out.print("\"");
        }
    }

}
