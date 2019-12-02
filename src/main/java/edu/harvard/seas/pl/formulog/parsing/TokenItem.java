package edu.harvard.seas.pl.formulog.parsing;

/*-
 * #%L
 * FormuLog
 * %%
 * Copyright (C) 2018 - 2019 President and Fellows of Harvard College
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

public class TokenItem {

	public final Token token;
	public final Object value;
	public final int line;
	public final int column;

	private TokenItem(Token token, Object value, int line, int column) {
		this.token = token;
		this.value = value;
		this.line = line;
		this.column = column;
	}

	@Override
	public String toString() {
		String s = "" + token;
		if (value != null) {
			s += "(" + value + ")";
		}
		return s + "@" + line + ":" + column;
	}
	
	public static TokenItem mkColon(int line, int column) {
		return new TokenItem(Token.COLON, null, line, column);
	}
	
	public static TokenItem mkComma(int line, int column) {
		return new TokenItem(Token.COMMA, null, line, column);
	}

	public static TokenItem mkDouble(double val, int line, int column) {
		return new TokenItem(Token.DOUBLE, val, line, column);
	}
	
	public static TokenItem mkEol(int line, int column) {
		return new TokenItem(Token.EOL, null, line, column);
	}
	
	public static TokenItem mkFloat(float val, int line, int column) {
		return new TokenItem(Token.FLOAT, val, line, column);
	}
	
	public static TokenItem mkFun(int line, int column) {
		return new TokenItem(Token.FUN, null, line, column);
	}
	
	public static TokenItem mkLong(long val, int line, int column) {
		return new TokenItem(Token.LONG, val, line, column);
	}
	
	public static TokenItem mkInput(int line, int column) {
		return new TokenItem(Token.INPUT, null, line, column);
	}
	
	public static TokenItem mkInt(int val, int line, int column) {
		return new TokenItem(Token.INT, val, line, column);
	}
	
	public static TokenItem mkOutput(int line, int column) {
		return new TokenItem(Token.OUTPUT, null, line, column);
	}
	
	public static TokenItem mkPeriod(int line, int column) {
		return new TokenItem(Token.PERIOD, null, line, column);
	}
	
	public static TokenItem mkSemicolon(int line, int column) {
		return new TokenItem(Token.SEMICOLON, null, line, column);
	}
	
	public static TokenItem mkString(String s, int line, int column) {
		return new TokenItem(Token.STRING, s, line, column);
	}
	
	public static TokenItem mkTurnstile(int line, int column) {
		return new TokenItem(Token.TURNSTILE, null, line, column);
	}
	
	public static TokenItem mkId(String id, int line, int column) {
		return new TokenItem(Token.ID, id, line, column);
	}
	
}
