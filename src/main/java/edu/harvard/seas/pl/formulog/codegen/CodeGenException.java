/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2022-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.codegen;

public class CodeGenException extends Exception {

  private static final long serialVersionUID = -3022070471185499421L;

  public CodeGenException(String message) {
    super(message);
  }

  public CodeGenException(Exception cause) {
    super(cause);
  }
}
