package formulog.db;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 Anonymous Institute
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



import java.util.Comparator;

import formulog.ast.Term;

public class ExampleComparator implements Comparator<Term[]> {

	@Override
	public int compare(Term[] xs, Term[] ys) {
		int xid = xs[0].getId();
		int yid = ys[0].getId();
		if (xid < yid) {
			return -1;
		} else if (xid > yid) {
			return 1;
		}
		
		xid = xs[2].getId();
		yid = ys[2].getId();
		if (xid < yid) {
			return -1;
		} else if (xid > yid) {
			return 1;
		}
		
		xid = xs[1].getId();
		yid = ys[1].getId();
		if (xid < yid) {
			return -1;
		} else if (xid > yid) {
			return 1;
		}
		return 0;
	}

}
