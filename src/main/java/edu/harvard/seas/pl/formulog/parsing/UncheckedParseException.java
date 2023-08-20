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

public class UncheckedParseException extends RuntimeException {

  private static final long serialVersionUID = -4969126551201111362L;
  private final int lineNo;
  private final String fileName;

  public UncheckedParseException(int lineNo, String message) {
    super(message);
    this.lineNo = lineNo;
    this.fileName = null;
  }

  public UncheckedParseException(int lineNo, Throwable cause) {
    super(cause);
    this.lineNo = lineNo;
    this.fileName = null;
  }

  public UncheckedParseException(ParseException e) {
    super(e.getMessage());
    this.lineNo = e.getLineNo();
    this.fileName = e.getFileName();
  }

  public int getLineNo() {
    return lineNo;
  }

  public String getFileName() {
    return fileName;
  }
}
