import pandas as pd 
import numpy as np
import sys


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
	def __le__(self, other):
		return( self < other or self == other)
	def __hash__(self): 
		return hash(( self.start_line, self.end_line, self.start_char, self.end_char))
	def subsumes(self, other):  # returns true if self subsumes the other_stmt
		left_sub = self.start_line < other.start_line or (self.start_line == other.start_line and self.start_char <= other.start_char)
		right_sub = self.end_line > other.end_line or (self.end_line == other.end_line and self.end_char >= other.end_char)
		return( left_sub and right_sub and not self == other)


def convert_row_to_stmts_no_calls( row):
	[s_startline, s_startchar, s_endline, s_endchar, 
	ess_startline, ess_startchar, ess_endline, ess_endchar, 
	lss_startline, lss_startchar, lss_endline, lss_endchar, filename] = row
	s = Stmt( s_startline - 1, s_startchar - 1, s_endline - 1, s_endchar)
	ess = Stmt( ess_startline - 1, ess_startchar - 1, ess_endline - 1, ess_endchar)
	lss = Stmt( lss_startline - 1, lss_startchar - 1, lss_endline - 1, lss_endchar)
	return( [s, ess, lss, filename])

def convert_row_to_stmts( row):
	[s_startline, s_startchar, s_endline, s_endchar, 
	ess_startline, ess_startchar, ess_endline, ess_endchar, 
	lss_startline, lss_startchar, lss_endline, lss_endchar, filename,
	cs_startline, cs_startchar, cs_endline, cs_endchar, cs_name, cs_filename] = row
	s = Stmt( s_startline - 1, s_startchar - 1, s_endline - 1, s_endchar)
	ess = Stmt( ess_startline - 1, ess_startchar - 1, ess_endline - 1, ess_endchar)
	lss = Stmt( lss_startline - 1, lss_startchar - 1, lss_endline - 1, lss_endchar)
	cs = Stmt( cs_startline - 1, cs_startchar - 1, cs_endline - 1, cs_endchar)
	return( [s, ess, lss, filename, cs, cs_name, cs_filename])

def keep_first_stmt( row1, s1, s1_file):
	if row1.file != s1_file: # if they're not in the same file they can't be overlapping
		return True
	s2 = row1.to_move
	s1_before = (s1.start_line < s2.start_line or (s1.start_line == s2.start_line and s1.start_char < s2.start_char))
	s1_after_no_overlap = (s1.start_line > s2.start_line or (s1.start_line == s2.start_line and s1.start_char > s2.start_char))
	s1_after_no_overlap = s1_after_no_overlap and (s1.end_line > s2.end_line or (s1.end_line == s2.end_line and s1.end_char > s2.end_char))
	return( s1_before or s1_after_no_overlap or s1 == s2) # we'll have removed duplicates at this point so 

def get_preamble():
	return("import javascript\n\nbindingset[filename]\npredicate stmtInUsefulFile( string filename) { \n")

def get_predicate_body( files):
	to_ret = "\tfilename = \""
	to_ret += "\"\n\tor filename = \"".join( files)
	to_ret += "\""
	return( to_ret)

def get_postamble():
	return("\n}\n\nfrom Stmt s\nwhere stmtInUsefulFile(s.getFile().toString())\nselect s.getLocation().getStartLine(), s.getLocation().getStartColumn(), s.getLocation().getEndLine(), s.getLocation().getEndColumn(), s.getFile()")

def generate_new_all_stmts():
	data = pd.read_csv("time_calls.csv", sep = ',', header=None)
	output = data.apply(convert_row_to_stmts, axis=1, result_type='expand')
	output.columns = ['to_move', 'swap_before', 'swap_after', 'file', 'call_stmt', 'call_name', 'call_file']
	output.drop( output[(output.to_move == output.swap_before) & (output.to_move == output.swap_after)].index, inplace=True) # delete rows that mean no swapping
	# get rid of statements overlapping
	output['keep_stmt'] = output.apply(lambda x: output.apply( keep_first_stmt, args=(x.to_move, x.file), axis=1).all(), axis=1)	
	output.drop_duplicates(inplace=True) # delete duplicate rows
	output = output[output.keep_stmt]    # delete overlapping rows
	# might not even need to sort
	output.sort_values(['file', 'swap_before', 'to_move', 'call_stmt', 'call_name', 'call_file'], inplace=True)
	# get the list of all the files
	files = np.unique(output.call_file.to_list() + output.file.to_list()).tolist()
	# then, see if there's any extra files in swaps.csv
	data = pd.read_csv("swaps.csv", sep = ',', header=None)
	output = data.apply(convert_row_to_stmts_no_calls, axis=1, result_type='expand')
	output.columns = ['to_move', 'swap_before', 'swap_after', 'file']
	output.drop( output[(output.to_move == output.swap_before) & (output.to_move == output.swap_after)].index, inplace=True) # delete rows that mean no swapping
	# get rid of statements overlapping
	output['keep_stmt'] = output.apply(lambda x: output.apply( keep_first_stmt, args=(x.to_move, x.file), axis=1).all(), axis=1)	
	output.drop_duplicates(inplace=True) # delete duplicate rows
	output = output[output.keep_stmt]    # delete overlapping rows
	# might not even need to sort
	output.sort_values(['file', 'swap_before', 'to_move'], inplace=True)
	# get the list of all the files
	files = np.unique(files + output.file.to_list()).tolist()
	ql_code = get_preamble() + get_predicate_body( files) + get_postamble()
	# now, print to getAllStmts_codeql.ql
	file = open( "getAllStmts_codeql.ql", 'w')
	file.write( ql_code)
	file.close()	


def generate_new_all_stmts_no_calls():
	data = pd.read_csv("swaps.csv", sep = ',', header=None)
	output = data.apply(convert_row_to_stmts_no_calls, axis=1, result_type='expand')
	output.columns = ['to_move', 'swap_before', 'swap_after', 'file']
	output.drop( output[(output.to_move == output.swap_before) & (output.to_move == output.swap_after)].index, inplace=True) # delete rows that mean no swapping
	# get rid of statements overlapping
	output['keep_stmt'] = output.apply(lambda x: output.apply( keep_first_stmt, args=(x.to_move, x.file), axis=1).all(), axis=1)	
	output.drop_duplicates(inplace=True) # delete duplicate rows
	output = output[output.keep_stmt]    # delete overlapping rows
	# might not even need to sort
	output.sort_values(['file', 'swap_before', 'to_move'], inplace=True)
	# get the list of all the files
	files = output.file.unique()
	ql_code = get_preamble() + get_predicate_body( files) + get_postamble()
	# now, print to getAllStmts_codeql.ql
	file = open( "getAllStmts_codeql.ql", 'w')
	file.write( ql_code)
	file.close()	

if len( sys.argv) != 2 or (sys.argv[1] != "calls" and sys.argv[1] != "nocalls"):
	print("Usage: python fake_external_data_getAllStmts.py calls/nocalls")
elif sys.argv[1] == "calls":
	generate_new_all_stmts()
else:
	generate_new_all_stmts_no_calls()
