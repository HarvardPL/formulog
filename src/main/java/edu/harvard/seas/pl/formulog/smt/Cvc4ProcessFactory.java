package edu.harvard.seas.pl.formulog.smt;

import java.io.IOException;

import edu.harvard.seas.pl.formulog.util.Util;

public class Cvc4ProcessFactory implements ExternalSolverProcessFactory {

	private static Cvc4ProcessFactory instance;

	private Cvc4ProcessFactory() {
		Util.assertBinaryOnPath("cvc4");
	}
	
	public static Cvc4ProcessFactory get() {
		if (instance == null) {
			synchronized (Cvc4ProcessFactory.class) {
				if (instance == null) {
					instance = new Cvc4ProcessFactory();
				}
			}
		}
		return instance;
	}
	
	@Override
	public Process newProcess() throws IOException {
		return Runtime.getRuntime().exec("cvc4 --lang smt --incremental");
	}
}
