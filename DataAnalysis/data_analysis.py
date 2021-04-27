import numpy as np 
import pandas as pd 
import re
import scipy.stats as stats
import matplotlib
import matplotlib.pylab as plt

class Stmt:
	def __init__(self, start_line, start_char, end_line, end_char):
		self.start_line = start_line
		self.start_char = start_char
		self.end_line = end_line
		self.end_char = end_char
	def __str__(self):
		return("[" + str(self.start_line) + ", " + str(self.start_char) + "; " + str(self.end_line) + ", " + str(self.end_char) + "]")
	def __eq__(self, other):
		return( self.start_line == other.start_line and self.end_line == other.end_line and self.start_char == other.start_char and self.end_char == other.end_char)
	def __lt__(self, other):
		return( self.start_line < other.start_line or (self.start_line == other.start_line and self.start_char < other.start_char))
	def __hash__(self):
		return id(self)
	def subsumes(self, other):  # returns true if self subsumes the other_stmt
		left_sub = self.start_line < other.start_line or (self.start_line == other.start_line and self.start_char <= other.start_char)
		right_sub = self.end_line > other.end_line or (self.end_line == other.end_line and self.end_char >= other.end_char)
		return( left_sub and right_sub and not self == other)

def convert_str_to_stmt( col):
	# use regex to split the stmt column, we're converting it from a string to Stmt object
	[start_line, start_char, end_line, end_char] = [int(i) for i in re.findall("[\w']+", col)] 
	return( Stmt( start_line, start_char, end_line, end_char))

def process_data_file( filename, is_calls = False):
	to_ret = pd.read_csv(filename, sep = '&', header=None)
	to_ret.columns = ['file', 'stmt_moved', 'var_name', 'time']
	to_ret.stmt_moved = to_ret.stmt_moved.apply(convert_str_to_stmt)
	# this is ugly, but all var_names look like TEMP_VAR_AUTOGEN***_RANDOM, where *** is the number we want
	if not is_calls:
		to_ret.var_name = to_ret.var_name.apply(lambda col: int(col.split("_")[2][7:])) 
	else:
		to_ret['nonloc_name'] = to_ret.var_name.apply(lambda col: "".join(col.split("_")[5])) 
		to_ret.var_name = to_ret.var_name.apply(lambda col: "".join(col.split("_")[4:6])) 
	return( to_ret)

def process_timing_file( filename):
	to_ret = pd.read_csv( filename, sep = ' ', header=None)
	to_ret.drop([0, 1, 2], inplace=True, axis=1) # delete the garbage initial columns
	to_ret.columns = ['test', 'time']
	to_ret.sort_values('test', inplace=True)
	to_ret.time = [float(t[1:t.index('s)')]) for t in to_ret.time]
	to_ret['time_avg'] = to_ret.groupby(['test'])['time'].transform('sum')/to_ret.groupby(['test'])['time'].transform('count')
	return( to_ret)

def sig_speed_res( row, pconf):
	if row.sig[1] < pconf: # this is the p value, if it's < pconf we have a significant result
		if row.sig[0] > 0:
			return( "SPEEDUP")
		elif row.sig[0] < 0:
			return( "SLOWDOWN")
	return("")

def gen_result_table_for_tests( no_swap_tests, swap_tests):
	pconf = 0.1
	to_ret = pd.merge( no_swap_tests[['test', 'time_avg']].drop_duplicates(), swap_tests[['test', 'time_avg']].drop_duplicates(), on='test', how='left')
	to_ret.columns = ['test', 'noswap_avg', 'swap_avg']
	is_sig = [stats.ttest_ind(no_swap_tests[no_swap_tests.test == t].time, swap_tests[swap_tests.test == t].time, equal_var=False) for t in swap_tests.test.unique()]
	to_ret["sig"] = is_sig
	to_ret["sig_result"] = to_ret.apply(sig_speed_res, args=(pconf,), axis=1)
	return( to_ret)

def gen_result_table_for_var_set( var_names, time_frame):
	to_ret = pd.DataFrame([get_result_for_var_name(v, time_frame) for v in var_names], columns = ['var_name', 'count', 'mean', 'num_above_mean', 'stdev', 'max_val', 'min_val'])
	to_ret.sort_values('var_name', inplace=True)
	return( to_ret)

def gen_result_table_for_all_vars( time_frame):
	return( gen_result_table_for_var_set( time_frame.var_name.unique(), time_frame))

def total_time_spent_awaiting( time_frame):
	return( time_frame.time.sum())

def gen_nonloc_calls_comparative_mean_table( noswap_frame, swap_frame):
	all_fcts = noswap_frame.nonloc_name.unique()
	noswap_times = [noswap_frame[noswap_frame.nonloc_name == v].time.mean() for v in all_fcts]
	swap_times = [swap_frame[swap_frame.nonloc_name == v].time.mean() for v in all_fcts]
	is_sig = [stats.ttest_ind(noswap_frame[noswap_frame.nonloc_name == v].time, swap_frame[swap_frame.nonloc_name == v].time, equal_var=False) for v in all_fcts]
	to_ret = pd.DataFrame(list( zip( all_fcts, noswap_times, swap_times)), columns = ['nonloc_name', 'noswap_mean', 'swap_mean'])
	to_ret["swap_faster"] = to_ret.apply(lambda row: "SPEED" if row.noswap_mean > row.swap_mean else "", axis=1)
	to_ret["sig"] = is_sig
	to_ret["sig_result"] = to_ret.apply(sig_speed_res, args=(pconf,), axis=1)
	to_ret.sort_values('nonloc_name', inplace=True)
	return( to_ret)	

def gen_comparative_mean_table( noswap_frame, swap_frame):
	all_vars = noswap_frame.var_name.unique()
	noswap_times = [noswap_frame[noswap_frame.var_name == v].time.mean() for v in all_vars]
	swap_times = [swap_frame[swap_frame.var_name == v].time.mean() for v in all_vars]
	is_sig = [stats.ttest_ind(noswap_frame[noswap_frame.var_name == v].time, swap_frame[swap_frame.var_name == v].time, equal_var=False) for v in all_vars]
	to_ret = pd.DataFrame(list( zip( all_vars, noswap_times, swap_times)), columns = ['var_name', 'noswap_mean', 'swap_mean'])
	to_ret["swap_faster"] = to_ret.apply(lambda row: "SPEED" if row.noswap_mean > row.swap_mean else "", axis=1)
	to_ret["sig"] = is_sig
	to_ret["sig_result"] = to_ret.apply(sig_speed_res, args=(pconf,), axis=1)
	to_ret.sort_values('var_name', inplace=True)
	return( to_ret)

def gen_jest_test_comparative_mean_table( noswap_frame, swap_frame):
	pconf = 0.1
	all_tests = noswap_frame.test_id.unique()
	noswap_times = [noswap_frame[noswap_frame.test_id == t].time.mean() for t in all_tests]
	swap_times = [swap_frame[swap_frame.test_id == t].time.mean() for t in all_tests]
	is_sig = [stats.ttest_ind(noswap_frame[noswap_frame.test_id == t].time, swap_frame[swap_frame.test_id == t].time, equal_var=False) for t in all_tests]
	to_ret = pd.DataFrame(list( zip( all_tests, noswap_times, swap_times)), columns = ['test_id', 'noswap_mean', 'swap_mean'])
	to_ret["swap_faster"] = to_ret.apply(lambda row: "SPEED" if row.noswap_mean > row.swap_mean else "", axis=1)
	to_ret["sig"] = is_sig
	to_ret["sig_result"] = to_ret.apply(sig_speed_res, args=(pconf,), axis=1)
	to_ret["suite_name"] = [noswap_frame[noswap_frame.test_id == t].suite_name.to_list()[0] for t in all_tests]
	to_ret.sort_values('test_id', inplace=True)
	return( to_ret)

def get_result_for_var_name( var_name, time_frame):
	var_time = time_frame[time_frame.var_name == var_name].time
	count = var_time.count()
	mean = var_time.mean()
	num_above_mean = var_time.apply(lambda t: t > mean).sum()
	stdev = var_time.std()
	max_val = var_time.max()
	min_val = var_time.min()
	return((var_name, count, mean, num_above_mean, stdev, max_val, min_val))

# print dataframe df to file specified
def printDFToFile( df, filename):
	f = open(filename, 'w');
	f.write(df.to_csv(index = False))
	f.close()

# it's already in dataframe form, since it's the output from an earlier processing
# script over the junit-unit-test.xml output, that just prints the dataframe
def process_jest_test_output( filename):
	to_ret = pd.read_csv( filename, header=None)
	to_ret.columns = [ 'test_id', 'time', 'suite_name', 'suite_total_tests', 'suite_time']
	to_ret.sort_values('test_id', inplace=True)
	return( to_ret)

# take as input a DF returned from process_jest_test_output
def get_test_timing_from_junit( junit_df):
	# columns should be test, time, time_avg
	to_ret = junit_df[["suite_name", "suite_time"]]
	to_ret.columns = ["test", "time"]
	to_ret['time_avg'] = to_ret.groupby(['test'])['time'].transform('sum')/to_ret.groupby(['test'])['time'].transform('count')
	to_ret.sort_values('test', inplace=True)
	return( to_ret)

def get_summary_jest_test_table( js_df):
	tests = js_df.test_id.unique()
	times = [js_df[js_df.test_id == t].time.mean() for t in tests]
	stdevs = [js_df[js_df.test_id == t].time.std() for t in tests]
	to_ret = pd.DataFrame(list( zip( tests, times, stdevs)), columns = ['test_id', 'time_mean', 'time_stdev'])
	to_ret["suite_name"] = [js_df[js_df.test_id == t].suite_name.to_list()[0] for t in tests]
	return( to_ret)

# expects output from gen_jest_test_comparative_mean_table
def scatterplot_test_speedup( js_df, proj_name):
	y = 1 - (js_df.swap_mean/js_df.noswap_mean) # y axis is the percentage speedup
	y = y.replace([np.inf, -np.inf], np.nan)
	y = y.dropna()
	y *= 100 # represent as a percentage
	x = range(0, len(y))
	sigs = js_df.sig_result
	sig_xs = [i for i in x if sigs[i] == "SPEEDUP"]
	sig_ys = [y[i] for i in sig_xs]
	avg = y.mean()
	# now create the plot
	plt.scatter(x, y, color='b', label="not significant", facecolor="none")
	plt.scatter(sig_xs, sig_ys, color='b', label="significant")
	plt.axhline(y=avg, color='r', linestyle='--', linewidth=2, label="mean")
	plt.axhline(y=0, color='k', linestyle='-', linewidth=1)	
	plt.xlabel("Test", fontsize=12)
	plt.ylabel("% Speedup after reordering", fontsize=12)
	plt.title("% Speedup for " + proj_name + " tests")
	plt.legend()
	plt.show()

# function to plot all runtimes from the swapped and not-swapped experiment runs, 
# for one specific test
def plot_test_times( swapped, notswapped, test_id):
	test_name = swapped.test_id.unique()[test_id]
	swap = swapped[swapped.test_id == test_name].time
	noswap = notswapped[notswapped.test_id == test_name].time
	xs = range(len(swap))
	plt.axhline(y=swap.mean(), color='k', linestyle='--', label="mean with reordering")
	plt.axhline(y=noswap.mean(), color='k', linestyle='dashdot', label="mean with original code")
	plt.scatter(xs, swap, color='b', label="with reordering")
	plt.scatter(xs, noswap, color='b', facecolor="none", label="original code")
	plt.xlabel("Experiment run", fontsize=14)
	plt.ylabel("Runtime (s)", fontsize=14)
	plt.title("Runtime for test " + str(test_id) + " for each experiment run", fontsize=16)
	plt.legend()
	plt.show()

# get total test suite timing
def get_total_test_timing(junit_df):
	tests = junit_df.test_id.unique()
	runtimes = junit_df.time
	num_tests = len(tests)
	num_experiments = int(len(runtimes)/num_tests)
	run_timing = [0]*num_experiments
	for i in range(len(runtimes)):
		run_timing[i % num_experiments] += runtimes[i]
	return(np.array(run_timing))
