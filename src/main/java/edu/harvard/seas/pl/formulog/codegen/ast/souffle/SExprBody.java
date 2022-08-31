package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

import edu.harvard.seas.pl.formulog.ast.Term;
import edu.harvard.seas.pl.formulog.ast.Var;

import java.util.List;

public class SExprBody implements SFunctorBody {

    private final List<Var> args;
    private final Term body;

    public SExprBody(List<Var> args_, Term body_) {
        args = args_;
        body = body_;
    }

    public Term getBody() {
        return body;
    }

    @Override
    public List<Var> getArgs() {
        return args;
    }

    @Override
    public SType getRetType() {
        return SIntType.INSTANCE;
    }

    @Override
    public boolean isStateful() {
        return false;
    }

}
