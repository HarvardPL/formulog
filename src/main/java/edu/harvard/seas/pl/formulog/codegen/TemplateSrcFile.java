package edu.harvard.seas.pl.formulog.codegen;

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

import java.io.*;

public abstract class TemplateSrcFile {

    private final String name;
    protected final CodeGenContext ctx;

    public TemplateSrcFile(String name, CodeGenContext ctx) {
        this.name = name;
        this.ctx = ctx;
    }

    void gen(File outDir) throws IOException, CodeGenException {
        try (InputStream is = CodeGenUtil.inputSrcFile(name);
             InputStreamReader isr = new InputStreamReader(is);
             BufferedReader br = new BufferedReader(isr);
             PrintWriter out = new PrintWriter(CodeGenUtil.outputSrcFile(outDir, name))) {
            gen(br, out);
            out.flush();
        }
    }

    abstract void gen(BufferedReader br, PrintWriter out) throws IOException, CodeGenException;

}
