package edu.harvard.seas.pl.formulog.parsing;

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

/**
 * An exception signifying a parsing error.
 *
 */
public class ParseException extends Exception {

	private static final long serialVersionUID = 1L;
	private final String fileName;
	private final int lineNo;

	/**
	 * Constructs an exception signifying a parsing error.
	 */
	public ParseException(String fileName, int lineNo, String message) {
		super(message);
		this.fileName = fileName;
		this.lineNo = lineNo;
	}

	/**
	 * Constructs an exception signifying a parsing error.
	 */
	public ParseException(int lineNo, String message) {
		this(null, lineNo, message);
	}

	public ParseException(UncheckedParseException e) {
		super(e.getMessage());
		this.fileName = e.getFileName();
		this.lineNo = e.getLineNo();
	}

	public String getFileName() {
		return fileName;
	}

	public int getLineNo() {
		return lineNo;
	}

}
