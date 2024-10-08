/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2019-2023 President and Fellows of Harvard College
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
package edu.harvard.seas.pl.formulog.validating;

public class InvalidProgramException extends Exception {

  private static final long serialVersionUID = 5958219607857975431L;

  /** Constructs an exception signifying an ill-formedness error. */
  public InvalidProgramException() {}

  /**
   * Constructs an exception signifying an ill-formedness error.
   *
   * @param message the error message
   */
  public InvalidProgramException(String message) {
    super(message);
  }

  /**
   * Constructs an exception signifying an ill-formedness error.
   *
   * @param cause the exception that caused this exception
   */
  public InvalidProgramException(Throwable cause) {
    super(cause);
  }

  /**
   * Constructs an exception signifying an ill-formedness error.
   *
   * @param message the error message
   * @param cause the exception that caused this exception
   */
  public InvalidProgramException(String message, Throwable cause) {
    super(message, cause);
  }

  /**
   * Constructs an exception signifying an ill-formedness error.
   *
   * @param message the error message
   * @param cause the exception that caused this exception
   * @param enableSuppression whether or not suppression is enabled or disabled
   * @param writableStackTrace whether or not the stack trace should be writable
   */
  public InvalidProgramException(
      String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
    super(message, cause, enableSuppression, writableStackTrace);
  }
}
