package edu.harvard.seas.pl.formulog.util;

/*-
 * #%L
 * FormuLog
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

import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Dataset {

	private final Set<Datum> data = Util.concurrentSet();

	public void addDataPoint(double val) {
		data.add(new Datum(val));
	}

	public int size() {
		return data.size();
	}

	public double computeSum() {
		double sum = 0;
		for (Datum d : data) {
			sum += d.val;
		}
		return sum;
	}

	public double computeMean() {
		assert size() > 0;
		return computeSum() / size();
	}

	public double computeStdDev() {
		double mean = computeMean();
		double varSum = 0;
		for (Datum d : data) {
			double delta = d.val - mean;
			varSum += delta * delta;
		}
		return Math.sqrt(varSum / (data.size() - 1));
	}

	public List<Double> computeMinMedianMax() {
		List<Datum> points = data.stream().sorted().collect(Collectors.toList());
		int n = size();
		double min = points.get(0).val;
		double max = points.get(n - 1).val;
		int mid = n / 2;
		double median = points.get(mid).val;
		if (n % 2 == 0) {
			median = (median + points.get(mid - 1).val) / 2;
		}
		return Arrays.asList(min, median, max);
	}

	public String getStatsString() {
		if (size() == 0) {
			return "-";
		}
		List<Double> mmm = computeMinMedianMax();
		return String.format("n=%d,mean=%1.1f,min=%1.1f,median=%1.1f,max=%1.1f,stddev=%1.1f", size(), computeMean(),
				mmm.get(0), mmm.get(1), mmm.get(2), computeStdDev());
	}

	private static class Datum implements Comparable<Datum> {

		public final double val;

		public Datum(double val) {
			this.val = val;
		}

		@Override
		public int compareTo(Datum o) {
			return Double.compare(val, o.val);
		}

	}

}
