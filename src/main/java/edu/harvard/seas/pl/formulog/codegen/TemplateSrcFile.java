package edu.harvard.seas.pl.formulog.codegen;

import java.io.*;

public abstract class TemplateSrcFile {

    private final String name;
    protected final CodeGenContext ctx;

    public TemplateSrcFile(String name, CodeGenContext ctx) {
        this.name = name;
        this.ctx = ctx;
    }

    void gen(File outDir) throws IOException {
        try (InputStream is = CodeGenUtil.inputSrcFile(name);
             InputStreamReader isr = new InputStreamReader(is);
             BufferedReader br = new BufferedReader(isr);
             PrintWriter out = new PrintWriter(CodeGenUtil.outputSrcFile(outDir, name))) {
            gen(br, out);
            out.flush();
        }
    }

    abstract void gen(BufferedReader br, PrintWriter out) throws IOException;

}
