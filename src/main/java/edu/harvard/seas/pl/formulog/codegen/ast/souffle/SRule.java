package edu.harvard.seas.pl.formulog.codegen.ast.souffle;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2022 President and Fellows of Harvard College
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

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.harvard.seas.pl.formulog.util.Pair;

public class SRule {

    private final SLit head;
    private final List<SLit> body;
    private List<Pair<Integer, int[]>> queryPlan;

    public SRule(SLit head, List<SLit> body) {
        this.head = head;
        this.body = body;
    }

    public SRule(SLit head, SLit... body) {
        this(head, Arrays.asList(body));
    }

    public List<SLit> getBody() {
        return Collections.unmodifiableList(body);
    }

    public void setQueryPlan(List<Pair<Integer, int[]>> queryPlan) {
        this.queryPlan = queryPlan;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(head);
        if (!body.isEmpty()) {
            sb.append(" :- ");
            String sep = "";
            if (body.size() > 1) {
                sep = "\n\t";
            }
            for (int i = 0; i < body.size(); ++i) {
                sb.append(sep);
                sb.append(body.get(i));
                if (i < body.size() - 1) {
                    sb.append(", ");
                }
            }
        }
        sb.append(".");
        if (queryPlan != null) {
            sb.append("\n");
            for (int i = 0; i < queryPlan.size(); ++i) {
                if (i == 0) {
                    sb.append(".plan ");
                } else {
                    sb.append(", ");
                }
                var p = queryPlan.get(i);
                sb.append(p.fst());
                sb.append(": (");
                var plan = p.snd();
                for (int j = 0; j < plan.length; ++j) {
                    sb.append(plan[j]);
                    if (j < plan.length - 1) {
                        sb.append(",");
                    }
                }
                sb.append(")");
            }
        }
        return sb.toString();
    }

}
