package edu.harvard.seas.pl.formulog.smt;

import java.io.IOException;

import edu.harvard.seas.pl.formulog.util.Util;

public class YicesProcessFactory implements ExternalSolverProcessFactory {

	private static YicesProcessFactory instance;

	private YicesProcessFactory() {
		Util.assertBinaryOnPath("yices-smt2");
	}
	
	public static YicesProcessFactory get() {
		if (instance == null) {
			synchronized (YicesProcessFactory.class) {
				if (instance == null) {
					instance = new YicesProcessFactory();
				}
			}
		}
		return instance;
	}
	
	@Override
	public Process newProcess() throws IOException {
		return Runtime.getRuntime().exec("yices-smt2 --incremental");
	}
}
