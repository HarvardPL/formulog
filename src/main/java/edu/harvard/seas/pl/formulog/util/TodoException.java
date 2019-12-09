package edu.harvard.seas.pl.formulog.util;

public class TodoException extends RuntimeException {

	private static final long serialVersionUID = 1L;

	public TodoException() {
		
	}

	public TodoException(String message) {
		super(message);
	}

	public TodoException(Throwable cause) {
		super(cause);
	}

	public TodoException(String message, Throwable cause) {
		super(message, cause);
	}

	public TodoException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
	}

}
