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
package edu.harvard.seas.pl.formulog.symbols.parameterized;

import edu.harvard.seas.pl.formulog.types.Types;
import java.util.ArrayList;
import java.util.List;

public abstract class AbstractParameterizedSymbol<B extends SymbolBase>
    implements ParameterizedSymbol {

  private final B base;
  private final List<Param> args;

  public AbstractParameterizedSymbol(B base, List<Param> args) {
    if (base.getNumParams() != args.size()) {
      throw new IllegalArgumentException(
          "Wrong number of parameters for symbol "
              + base
              + ", which has parameter arity "
              + base.getNumParams()
              + " but received parameters "
              + args);
    }
    this.base = base;
    this.args = new ArrayList<>();
    List<ParamKind> kinds = base.getParamKinds();
    for (int i = 0; i < kinds.size(); ++i) {
      Param param = new Param(args.get(i).getType(), kinds.get(i));
      this.args.add(param);
    }
  }

  @Override
  public int getArity() {
    return base.getArity();
  }

  @Override
  public String toString() {
    String s = base.toString();
    s += "<";
    for (int i = 0; i < args.size(); ++i) {
      s += args.get(i);
      if (i < args.size() - 1) {
        s += ", ";
      }
    }
    return s + ">";
  }

  @Override
  public B getBase() {
    return base;
  }

  @Override
  public List<Param> getArgs() {
    return args;
  }

  @Override
  public boolean isGround() {
    for (Param arg : args) {
      if (Types.containsTypeVarOrOpaqueType(arg.getType())) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((args == null) ? 0 : args.hashCode());
    result = prime * result + ((base == null) ? 0 : base.hashCode());
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    @SuppressWarnings("rawtypes")
    AbstractParameterizedSymbol other = (AbstractParameterizedSymbol) obj;
    if (args == null) {
      if (other.args != null) return false;
    } else if (!args.equals(other.args)) return false;
    if (base == null) {
      if (other.base != null) return false;
    } else if (!base.equals(other.base)) return false;
    return true;
  }
}
