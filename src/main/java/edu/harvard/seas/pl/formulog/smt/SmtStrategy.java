package edu.harvard.seas.pl.formulog.smt;

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


public class SmtStrategy {

	public enum Tag {
		QUEUE,
		
		BEST_MATCH,
		
		PER_THREAD_QUEUE,
		
		PER_THREAD_BEST_MATCH,
		
		PER_THREAD_PUSH_POP,
		
		PER_THREAD_NAIVE,
		
		;
	}

	private final Tag tag;
	private final Object metadata;

	public SmtStrategy(Tag tag, Object metadata) {
		this.tag = tag;
		this.metadata = metadata;
	}

	public Tag getTag() {
		return tag;
	}

	public Object getMetadata() {
		return metadata;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((metadata == null) ? 0 : metadata.hashCode());
		result = prime * result + ((tag == null) ? 0 : tag.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		SmtStrategy other = (SmtStrategy) obj;
		if (metadata == null) {
			if (other.metadata != null)
				return false;
		} else if (!metadata.equals(other.metadata))
			return false;
		if (tag != other.tag)
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "SmtStrategy [tag=" + tag + ", metadata=" + metadata + "]";
	}

}
