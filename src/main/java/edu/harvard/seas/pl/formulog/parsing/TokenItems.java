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

public final class TokenItems {

	private TokenItems() {
		throw new AssertionError("impossible");
	}
	
	public static final TokenItem colon = new TokenItem(Token.COLON, null);
	public static final TokenItem comma = new TokenItem(Token.COMMA, null);
	public static final TokenItem fun = new TokenItem(Token.FUN, null);
	public static final TokenItem input = new TokenItem(Token.INPUT, null);
	public static final TokenItem output = new TokenItem(Token.OUTPUT, null);
	public static final TokenItem period = new TokenItem(Token.PERIOD, null);
	public static final TokenItem semicolon = new TokenItem(Token.SEMICOLON, null);
	public static final TokenItem turnstile = new TokenItem(Token.TURNSTILE, null);
	
}
