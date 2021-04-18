import pandas as pd
import functools as ft
import numpy as np
import sys

# simple python script for making the reordering
# takes in a list of: statement to be moved, place it should go, and probably the file location
# we're going to need to make sure the information includes line, and start/end characters of the statements
# because generally a statement is a whole line but not necessarily

# running jest: after doing the  reordering, run:
# `npm run test:unit -- --watch --runInBand`
# watch: this options specifies to only run the tests that rely on files that have changed since the last commit
# runInBand: run the tests sequentially

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
		return id(self)
	def subsumes(self, other):  # returns true if self subsumes the other_stmt
		left_sub = self.start_line < other.start_line or (self.start_line == other.start_line and self.start_char <= other.start_char)
		right_sub = self.end_line > other.end_line or (self.end_line == other.end_line and self.end_char >= other.end_char)
		return( left_sub and right_sub and not self == other)

class ParseTreeNode:
	def __init__(self, child_list, stmt):
		self.stmt = stmt
		self.child_list = child_list
		self.is_leaf = False
		self.text = [[]]
		self.parent = None
		if len(child_list) == 0:
			self.is_leaf = True
		for c in child_list:
			c.parent = self
	def __set_self_text(self, file_contents):
		if self.is_leaf:
			self.text = [get_stmt( self.stmt, file_contents)] # return array of strings representing the lines of the statement
			return
		# if we're here it means there is at least one child
		current_child = self.child_list[0]
		# get the text from the beginning of the stmt until the beginning of the first child node
		subs = 0 if current_child.stmt.start_line == self.stmt.start_line else 1
		self.text = [get_stmt( Stmt(self.stmt.start_line, self.stmt.start_char, current_child.stmt.start_line, current_child.stmt.start_char - subs), file_contents)]
		for ind in range(1, len(self.child_list)):
			next_child = self.child_list[ind]
			# print(Stmt(current_child.stmt.end_line, current_child.stmt.end_char + 1, next_child.stmt.start_line, next_child.stmt.start_char))
			self.text += [get_stmt( Stmt(current_child.stmt.end_line, current_child.stmt.end_char + 1, next_child.stmt.start_line, next_child.stmt.start_char - 1), file_contents)]
			current_child = next_child
		adds = 0 if len(self.child_list) == 1 and self.stmt.start_line == self.stmt.end_line and self.stmt.end_char > self.child_list[0].stmt.end_char else 1
		self.text += [get_stmt( Stmt(current_child.stmt.end_line, current_child.stmt.end_char + adds, self.stmt.end_line, self.stmt.end_char), file_contents)]
	def set_text(self, file_contents):
		self.__set_self_text(file_contents)
		for c in self.child_list:
			c.set_text(file_contents)
	def get_text(self):
		to_ret = self.text[0].copy()
		for ind in range(1, len(self.text)):
			to_ret += self.child_list[ind - 1].get_text()
			to_ret += self.text[ind].copy()
		return( to_ret)
	def print(self):
		print_array_newline_sep( self.get_text())
	def __hash__(self):
		return id(self)


def count_tree(rnode):
	count = 1
	for c in rnode.child_list:
		count += count_tree(c)
	return count

# text is an array of arrays, just the first element
# is an array of strings
# we want to get the index of the element with "await" in it
# there should just be one (but if there's more than one we can just do the first one)
def get_index_with_await( text, swapping_last = False):
	indices = [(k, i) for k in range(len(text)) for i in range( 0, len(text[k])) if text[k][i].count("await ") > 0]
	if len(indices) > 1 or len(indices) == 0:
		print("WHAT IS GOING ON: " + str(text))
		return( (-1, -1))
	if swapping_last:
		return( indices[-1]) # if we're reordering forward, get the last await
	return( indices[0]) # otherwise, get the first await 

def corresp_paren(p):
	return {
		'(' : ')',
		')' : '(',
		'[' : ']',
		']' : '[',
		'{' : '}',
		'}' : '{'
	}.get(p, p) # just return p itself as a default if it's not in the dict

def build_paren_stack( a_string):
	paren_stack = ""
	for c in a_string:
		if c == "(" or c == "{" or c == "[":
			paren_stack += c
		elif c == ")" or c == "}" or c == "]":
			if len(paren_stack) > 0 and paren_stack[-1] == corresp_paren(c):
				paren_stack = paren_stack[ : -1]
			else:
				paren_stack += c
	return( paren_stack)


# we need to match the parens before and after the awaits, in case 
# note: no need to look through the text of the child_list, since these are self-contained 
# statements and so won't include closing/opening parens in part of the enclosing stmt, which 
# is the statement we're parsing 
def get_compensating_parens( text, text_ind, ind_to_split_at):
	if ind_to_split_at == -1: # then there was an error
		return( -1, -1)
	start_text = text[text_ind][0 : ind_to_split_at]
	end_text = text[text_ind][ ind_to_split_at + 1 : ]
	# get the text we're going to split: 
	split_text = text[text_ind][ind_to_split_at]
	front_paren_stack = build_paren_stack( ''.join(start_text) + split_text[0: split_text.index('await')])
	end_paren_stack = build_paren_stack( split_text[ split_text.index('await') + len('await') : ] + ''.join(end_text))
	if build_paren_stack(front_paren_stack + end_paren_stack) != "":
		#raise ValueError("Mismatched parens in: " + text[text_ind][ind_to_split_at])
		return( -1, -1)
	return( front_paren_stack, end_paren_stack)


# this is like move_stmt, but instead of just shifting the statement, we're actually going 
# to split it into an initial promise creation:
# 	var temp = < portion of the statement after the await >
# this goes where the statement would be moved to
#	< portion of the statement before the await > = await temp
# this should just involve changing the text() of the moved node and the placeholder node
# no scoping issues should ensue, since we're moving the whole statement
def move_and_split_await( root_node, root_map, stmt_to_move, stmt_to_move_before, temp_var_name, add_timing = False, filename = ""):
	node_to_move = root_map[stmt_to_move]
	node_to_move_before = root_map[stmt_to_move_before]
	# updates required:
	# remove node_to_move from its parent's child list
	# then, add it before stmt_to_move_before
	# NEW ITEM: update the text (using temp_var_name as specified)
	# when we remove node_to_move from the child list: 
	# 	-- just replace it with a new, blank node but with the old stmt as the stmt
	# 		-- then, it's not blank any more: the text is the corresponding "everything before the await" = await temp_var_name
	#		-- and, when we move the node, we're actually replacing the text to be var temp_var_name = "everything after the await" 
	#		-- also, split the child node list
	#	-- and, replace it in the node_map
	old_pos_node = ParseTreeNode( [], stmt_to_move)
	# now, compute the index to split at 
	(text_ind, ind_to_split_at) = get_index_with_await(node_to_move.text)
	#pre-compute paren stacks so we can catch all errors at once
	(front_paren_stack, end_paren_stack) = get_compensating_parens( node_to_move.text, text_ind, ind_to_split_at)
	if ind_to_split_at == -1 or front_paren_stack == -1: # then this is a problem, and we just won't do the reordering
		print("There's an issue and we can't automatically swap the following statement: ")
		node_to_move.print()
		print("With the following statement: ")
		node_to_move_before.print()
		print("DONE REPORTING PROBLEMS")
		# return( root_node, root_map, 0)
		return(0)
	# split both the text array and the child_list
	start_text = node_to_move.text[text_ind][0 : ind_to_split_at]
	end_text = node_to_move.text[text_ind][ ind_to_split_at + 1 : ]
	start_child_list = node_to_move.child_list[0 : ind_to_split_at]
	end_child_list = node_to_move.child_list[ ind_to_split_at :]
	# get the text we're going to split: 
	split_text = node_to_move.text[text_ind][ind_to_split_at]
	string_before_await = split_text[0: split_text.index('await')]
	string_after_await = split_text[ split_text.index('await') + len('await') : ]
	if build_paren_stack(string_after_await) != "":
		return( 0)
	# now, add the new updates to the strings
	# don't forget the parens
	string_before_await = string_before_await + " await " + temp_var_name + end_paren_stack
	string_after_await = "var " + temp_var_name + " = " + front_paren_stack + string_after_await
	# and, set up the nodes
	# starting off the same as before
	if node_to_move.parent != None:
		child_list_to_rem_from = node_to_move.parent.child_list
		child_list_to_rem_from[child_list_to_rem_from.index(node_to_move)] = old_pos_node
	root_map[stmt_to_move] = old_pos_node
	if node_to_move_before.parent != None:
		child_list_to_add_to = node_to_move_before.parent.child_list
		child_list_to_add_to.insert( child_list_to_add_to.index(node_to_move_before), node_to_move)
		node_to_move_before.parent.text.insert( child_list_to_add_to.index(node_to_move_before), [""])
	node_to_move.parent = node_to_move_before.parent
	# now, update the text and child_lists in node_to_move and old_pos_node:
	# node_to_move gets the string after await (i.e. the promise creation we want to move earlier)
	# and, gets the end_child_list (for the same reason)
	bad_paren_start = ""
	bad_parens = False
	if add_timing:
		timing_pre_text = "var TIMING_" + temp_var_name + " = perf_hooks.performance.now();\n "
		timing_post_text = "console.log(\"" + filename + "& " + str(old_pos_node.stmt) + "& " + temp_var_name + "& \" + (perf_hooks.performance.now() - TIMING_" + temp_var_name + "));\n "
		new_await_timing_var = "await " + temp_var_name + end_paren_stack + ";\n "
		string_before_await = split_text[0: split_text.index('await')]
		# can't add timing if the await is in the middle of a statement, for example like multiassignment in kactus's utils.ts
		# so in this case just put the timing before the entire statement
		if build_paren_stack(string_before_await) != "":
			bad_parens = True
		if len( str.strip(string_before_await)) > 0:
			# only create this variable if we actually need it (just having it hanging out alone at the end of string_before_await is an error, but then it's also an error if created but never used)
			string_before_await += " AWAIT_VAR_TIMING_" + temp_var_name
			new_await_timing_var = "var AWAIT_VAR_TIMING_" + temp_var_name + " = " + new_await_timing_var 
		if not bad_parens:
			string_before_await = timing_pre_text + new_await_timing_var + timing_post_text + string_before_await
		else:
			bad_paren_start = timing_pre_text + new_await_timing_var + timing_post_text
	node_to_move.text = [[string_after_await] + end_text]
	node_to_move.child_list = end_child_list
	old_pos_node.text = [merge_into_first_string_of_list( start_text, bad_paren_start) + [string_before_await]]
	old_pos_node.child_list = start_child_list
	# return( root_node, root_map)
	return(1)


# this relies on the earlier swaps already being done
def move_await_later( root_node, root_map, stmt_to_move, stmt_to_move_after, temp_var_name, add_timing = False, filename = ""):
	swapping_last = True
	node_to_move = root_map[stmt_to_move]
	node_to_move_after = root_map[stmt_to_move_after]
	# updates required:
	# remove node_to_move from its parent's child list
	# then, add it before stmt_to_move_before
	# NEW ITEM: update the text (using temp_var_name as specified)
	# when we remove node_to_move from the child list: 
	# 	-- just replace it with a new, blank node but with the old stmt as the stmt
	# 		-- then, it's not blank any more: the text is the corresponding "everything before the await" = await temp_var_name
	#		-- and, when we move the node, we're actually replacing the text to be var temp_var_name = "everything after the await" 
	#		-- also, split the child node list
	#	-- and, replace it in the node_map
	old_pos_node = ParseTreeNode( [], stmt_to_move)
	# now, compute the index to split at 
	(text_ind, ind_to_split_at) = get_index_with_await(node_to_move.text, swapping_last)
	#pre-compute paren stacks so we can catch all errors at once
	(front_paren_stack, end_paren_stack) = get_compensating_parens( node_to_move.text, text_ind, ind_to_split_at)
	if ind_to_split_at == -1 or front_paren_stack == -1: # then this is a problem, and we just won't do the reordering
		print("There's an issue and we can't automatically swap the following statement: ")
		node_to_move.print()
		print("With the following statement: ")
		node_to_move_after.print()
		print("DONE REPORTING PROBLEMS")
		# return( root_node, root_map, 0)
		return(0)
	# split both the text array and the child_list
	start_text = node_to_move.text[text_ind][0 : ind_to_split_at]
	end_text = node_to_move.text[text_ind][ ind_to_split_at + 1 : ]
	start_child_list = node_to_move.child_list[0 : ind_to_split_at]
	end_child_list = node_to_move.child_list[ ind_to_split_at :]
	# get the text we're going to split: 
	split_text = node_to_move.text[text_ind][ind_to_split_at]
	string_before_await = split_text[0: split_text.rindex('await')]
	string_after_await = split_text[ split_text.rindex('await') + len('await') : ]
	if build_paren_stack(string_after_await) != "":
		return( 0)
	new_await_var = "var " + temp_var_name + "_LATER = " + front_paren_stack + split_text[ split_text.rindex('await') + len('await') : ]
	# if len( str.strip(string_before_await)) > 0:
		# string_before_await = string_before_await + " " + temp_var_name + "_LATER"
	# if build_paren_stack(string_before_await) != "": # the addition of the varname doesnt change this funcionality
	# 	# don't even split the text any more
	# 	node_to_split.text = [[timing_pre_text]+ node_to_split.text[text_ind] + ["\n" + timing_post_text]]
	# else:
	node_to_move.text[text_ind] = start_text + [new_await_var] + end_text + [end_paren_stack]
	placeholder_node = ParseTreeNode([], None)
	placeholder_node.parent = node_to_move
	node_to_move.child_list.insert( ind_to_split_at, placeholder_node)
	node_to_move.text.insert(ind_to_split_at, [""])
	# now, add the await to the node to move after
	actual_await_node = ParseTreeNode([], None)
	actual_await_node.parent = node_to_move_after
	actual_await_node.text = [[string_before_await + "await " + temp_var_name + "_LATER"]]
	if add_timing:
		timing_pre_text = "var TIMING_" + temp_var_name + "_LATER = perf_hooks.performance.now();\n "
		timing_post_text = "console.log(\"" + filename + "& " + str(old_pos_node.stmt) + "& " + temp_var_name + "& \" + (perf_hooks.performance.now() - TIMING_" + temp_var_name + "_LATER));\n "
		actual_await_node.text = [[timing_pre_text + timing_post_text + actual_await_node.text[0][0]]]
	# make room in the parent node, make sure to add it at the end
	node_to_move_after.text += [[""]]
	node_to_move_after.child_list += [actual_await_node]
	return( 1)	

def merge_into_first_string_of_list( string_list, to_merge):
	if string_list == []:
		return( [to_merge])
	string_list[0] = to_merge + string_list[0]
	return( string_list)

def time_await( root_node, root_map, stmt_to_time, temp_var_name, filename):
	node_to_time = root_map[stmt_to_time]
	# all we care about here is the await, we;re just updating the text 
	(text_ind, ind_to_split_at) = get_index_with_await(node_to_time.text)
	(front_paren_stack, end_paren_stack) = get_compensating_parens( node_to_time.text, text_ind, ind_to_split_at)
	if ind_to_split_at == -1 or front_paren_stack == -1: # then this is a problem, and we just won't do the reordering
		print("There's an issue and we can't automatically time the following statement: ")
		node_to_time.print()
		print("DONE REPORTING PROBLEMS")
		return( 0)
	# split both the text array and the child_list
	start_text = node_to_time.text[text_ind][0 : ind_to_split_at]
	end_text = node_to_time.text[text_ind][ ind_to_split_at + 1 : ]
	# get the text we're going to split: 
	split_text = node_to_time.text[text_ind][ind_to_split_at]
	# string_after_await = split_text[ split_text.index('await') + len('await') : ]
	# now, add the new updates to the strings
	# don't forget the parens
	# string_after_await = "var " + temp_var_name + " = " + front_paren_stack + string_after_await
	# always add timing
	timing_pre_text = "var TIMING_" + temp_var_name + " = perf_hooks.performance.now();\n "
	timing_post_text = "console.log(\"" + filename + "& " + str(node_to_time.stmt) + "& " + temp_var_name + "& \" + (perf_hooks.performance.now() - TIMING_" + temp_var_name + "));\n "
	new_await_timing_var = "await " + front_paren_stack + split_text[ split_text.index('await') + len('await') : ]
	string_before_await = split_text[0: split_text.index('await')]
	if len( str.strip(string_before_await)) > 0:
		string_before_await = string_before_await +  " AWAIT_VAR_TIMING_" + temp_var_name 
		new_await_timing_var = "var AWAIT_VAR_TIMING_" + temp_var_name + " = " +  new_await_timing_var
	string_timing_await = timing_pre_text + new_await_timing_var
	if build_paren_stack(string_before_await) != "": # the addition of the varname doesnt change this funcionality
		# don't even split the text any more
		node_to_time.text[text_ind] = [timing_pre_text] + node_to_time.text[text_ind] + ["\n" + timing_post_text]
	else:
		node_to_time.text[text_ind] = start_text + [string_timing_await]+ end_text + [end_paren_stack + timing_post_text + string_before_await]
	placeholder_node = ParseTreeNode([], None)
	placeholder_node.parent = node_to_time
	node_to_time.child_list.insert( ind_to_split_at, placeholder_node)
	node_to_time.text.insert(ind_to_split_at, [""])
	return( 1)

def time_call( root_node, root_map, stmt_to_time, temp_var_name, filename):
	node_to_time = root_map[stmt_to_time]
	# all we care about here is the await, we;re just updating the text 
	# unlike where we were timing the awaits, now we're actually timing the whole statement and have no
	# need to split it. all we do is put timing code around the statement
	timing_pre_text = "var TIMING_" + temp_var_name + " = perf_hooks.performance.now();\n "
	timing_post_text = "console.log(\"" + filename + "& " + str(node_to_time.stmt) + "& " + temp_var_name + "& \" + (perf_hooks.performance.now() - TIMING_" + temp_var_name + "));\n "
	placeholder_nodes = (ParseTreeNode([], None), ParseTreeNode([], None))
	placeholder_nodes[0].parent = node_to_time
	placeholder_nodes[1].parent = node_to_time
	node_to_time.child_list.insert( 0, placeholder_nodes[0])
	node_to_time.child_list += [placeholder_nodes[1]]
	node_to_time.text.insert(0, [timing_pre_text])
	node_to_time.text += [[timing_post_text]]
	return( 1)

def move_stmt( root_node, root_map, stmt_to_move, stmt_to_move_before):
	node_to_move = root_map[stmt_to_move]
	node_to_move_before = root_map[stmt_to_move_before]
	# updates required:
	# remove node_to_move from its parent's child list
	# then, add it before stmt_to_move_before
	# when we remove node_to_move from the child list: 
	# 	-- just replace it with a new, blank node but with the old stmt as the stmt
	#	-- and, replace it in the node_map
	child_list_to_rem_from = node_to_move.parent.child_list
	placeholder_node = ParseTreeNode( [], stmt_to_move)
	child_list_to_rem_from[child_list_to_rem_from.index(node_to_move)] = placeholder_node
	root_map[stmt_to_move] = placeholder_node
	child_list_to_add_to = node_to_move_before.parent.child_list
	child_list_to_add_to.insert( child_list_to_add_to.index(node_to_move_before), node_to_move)
	node_to_move_before.parent.text.insert( child_list_to_add_to.index(node_to_move_before), [""])
	node_to_move.parent = node_to_move_before.parent
	return( root_node, root_map)

def convert__file_spec_stmt_list_to_tree( stmt_list, file_contents): 
	# can iterate through the dataframe
	# probably need some recursive setup here, but this is going to be the wrapper helper function
	# first, make a root statement that encompasses the whole file
	root_stmt = Stmt(0, 0, len(file_contents) - 1, len(file_contents[-1]))
	[root_node, root_map] = create_subsumed( [root_stmt] + stmt_list, 0, dict([]))[1: ]
	return( root_node, root_map)

def create_subsumed( stmt_list, cur_ind, stmt_node_map):
	if not cur_ind < len(stmt_list):
		raise ValueError("Index must be less than the length of the stmt array")
	child_list = []
	current_stmt = stmt_list[ cur_ind]
	while cur_ind < len(stmt_list) - 1 and current_stmt.subsumes( stmt_list[ cur_ind + 1]):
		[cur_ind, next_node, stmt_node_map] = create_subsumed( stmt_list, cur_ind + 1, stmt_node_map)
		child_list += [ next_node]
		# cur_ind += 1
	cur_node = ParseTreeNode( child_list, current_stmt)
	stmt_node_map[current_stmt] = cur_node
	return( cur_ind, cur_node, stmt_node_map)

def convert_string_to_stmt( row):
	stmt_string = row.stmt
	stmt_string = stmt_string.split(",")
	if len(stmt_string) != 4:
		raise ValueError("This string should represent a stmt, which has 4 ints for position")
	return( Stmt( int(stmt_string[0]) - 1, int(stmt_string[1]) - 1, int(stmt_string[2]) - 1, int(stmt_string[3])))

# convert a row of QL output to a list of statements
# we're subtracting 1 from the line numbers since the queries report starting at line 1 
# but we need line 0 for the file
def convert_row_to_stmts( row):
	[s_startline, s_startchar, s_endline, s_endchar, 
	ess_startline, ess_startchar, ess_endline, ess_endchar, 
	lss_startline, lss_startchar, lss_endline, lss_endchar, filename] = row
	s = Stmt( s_startline - 1, s_startchar - 1, s_endline - 1, s_endchar)
	ess = Stmt( ess_startline - 1, ess_startchar - 1, ess_endline - 1, ess_endchar)
	lss = Stmt( lss_startline - 1, lss_startchar - 1, lss_endline - 1, lss_endchar)
	return( [s, ess, lss, filename])

def convert_row_to_stmts_with_calls( row):
	[s_startline, s_startchar, s_endline, s_endchar, 
	ess_startline, ess_startchar, ess_endline, ess_endchar, 
	lss_startline, lss_startchar, lss_endline, lss_endchar, filename,
	cs_startline, cs_startchar, cs_endline, cs_endchar, cs_name, cs_filename] = row
	s = Stmt( s_startline - 1, s_startchar - 1, s_endline - 1, s_endchar)
	ess = Stmt( ess_startline - 1, ess_startchar - 1, ess_endline - 1, ess_endchar)
	lss = Stmt( lss_startline - 1, lss_startchar - 1, lss_endline - 1, lss_endchar)
	cs = Stmt( cs_startline - 1, cs_startchar - 1, cs_endline - 1, cs_endchar)
	return( [s, ess, lss, filename, cs, cs_name, cs_filename])

def convert_row_to_stmt( row):
	[s_startline, s_startchar, s_endline, s_endchar, filename] = row
	s = Stmt( s_startline - 1, s_startchar - 1, s_endline - 1, s_endchar)
	return( [s, filename])


def keep_first_stmt( row1, s1, s1_file):
	if row1.file != s1_file: # if they're not in the same file they can't be overlapping
		return True
	s2 = row1.to_move
	s1_before = (s1.start_line < s2.start_line or (s1.start_line == s2.start_line and s1.start_char < s2.start_char))
	s1_after_no_overlap = (s1.start_line > s2.start_line or (s1.start_line == s2.start_line and s1.start_char > s2.start_char))
	s1_after_no_overlap = s1_after_no_overlap and (s1.end_line > s2.end_line or (s1.end_line == s2.end_line and s1.end_char > s2.end_char))
	return( s1_before or s1_after_no_overlap or s1 == s2) # we'll have removed duplicates at this point so 


# return array of strings representing the lines of the statement
def get_stmt(stmt, file_contents):
	ind = stmt.start_line
	if ind == stmt.end_line and (len(file_contents[ind]) < stmt.start_char or stmt.end_char == -1):
		return []
	# special case for the statement only being one character -- seems to happen with "{" after generic classes
	if ind == stmt.end_line and stmt.start_char == stmt.end_char and not (ind == 0 and stmt.start_char == 0): # fake root node
		return( [ file_contents[ ind][ stmt.start_char : stmt.end_char + 1 ]])
	# special case if the stmt is only on one line
	if ind == stmt.end_line:
		adds = 1 if len(file_contents[ind]) > stmt.end_char else 0
		end_char = ";" if (adds == 1 and file_contents[ ind][ stmt.end_char] == ";") else ""
		end_char = "," if (adds == 1 and file_contents[ ind][ stmt.end_char] == ",") else end_char
		return( [ file_contents[ ind][ stmt.start_char : stmt.end_char ] + end_char]) 
	stmt_cont = []
	if not len(file_contents[ind]) < stmt.start_char:
		stmt_cont = [ file_contents[ ind][ stmt.start_char :]]
	ind = ind + 1
	while ind < stmt.end_line:
		stmt_cont += [ file_contents[ ind]]
		ind = ind + 1
	stmt_cont += [ file_contents[ ind][ 0 : stmt.end_char + 1]]
	return( stmt_cont)

# print an array (should be strings), with each array entry on a new line
# here used to print out the contents of a file, post split on newline
def print_array_newline_sep( to_print):
	print( ft.reduce( lambda a, b: a + "\n" + b, to_print, ""))

# save a copy of a specified file (name is oldname_old)
def save_old_copy( filename, file_contents):
	print( "Modifying -- " + filename + " -- but not saving an old copy")
	# file = open( filename + "_old", 'w')
	# file.write( file_contents)
	# file.close()

def reprocess_file_name( all_stmts):
	org_root = "/home/ellen/Documents/odasa/projects/kactus/revision-2020-January-06--15-50-46/src"
	new_root = "/home/ellen/Documents/ASJProj/TESTING_reordering/kactus"
	all_stmts['file'] = all_stmts.apply( change_string_root, args=(org_root, new_root), axis=1)

def just_add_timing( dat, full_stmts, print_to_file = False, num_to_swap = -1, time_these_calls = None):
	if time_these_calls is not None:
		add_calls_timing( time_these_calls[ ~ time_these_calls.call_file.isin( dat.file)], full_stmts, print_to_file, -1) 
	df = dat
	if num_to_swap != -1:
		df = pd.DataFrame.head( dat, n = num_to_swap)
	files = df.file.unique()
	for f in files:
		file = open(f, 'r')
		file_contents = file.read()
		file.close()
		if print_to_file:
			# save a copy of the file 
			save_old_copy(f, file_contents)
		file_contents = file_contents.split("\n")
		swaps = df[ df.file == f][['to_move', 'swap_before', 'swap_after']] # they'll already be sorted
		all_stmts = full_stmts[full_stmts.file == f]
		all_stmts.sort_values(['file','stmt'], inplace=True)
		# create the parse tree for this whole file
		(rnode, rmap) = convert__file_spec_stmt_list_to_tree( all_stmts.stmt.to_list(), file_contents)
		rnode.set_text( file_contents)
		add_swaps_to_all_stmt( all_stmts, swaps)
		perf_hooks_added = [False]
		time_one_file( swaps, rnode, rmap, f, do_time, perf_hooks_added)
		if time_these_calls is not None:
			calls = time_these_calls[ time_these_calls.call_file == f][['call_stmt', 'call_name']]
			calls['call_stmt'] = calls.apply( lambda row: all_stmts[all_stmts.stmt == row.call_stmt].stmt.to_list()[0], axis=1) 
			time_one_file( calls, rnode, rmap, f, do_time_call, perf_hooks_added)
		if print_to_file:
			file = open( f, 'w')
			file.write(ft.reduce( lambda a, b: join_stmts(a, b), rnode.get_text(), "").lstrip())
			file.close()
		else:
			print("PROCESSING----------------------------------------------------")
			print(f)
			print("FILE CONTENTS BELOW-------------------------------------------")
			print_array_newline_sep(rnode.get_text())

def break_stmt( root_node, root_map, stmt_to_break, breaking_text, filename):
	node_to_time = root_map[stmt_to_break]
	# all we care about here is the await, we;re just updating the text 
	# unlike where we were timing the awaits, now we're actually timing the whole statement and have no
	# need to split it. all we do is put timing code around the statement
	throws_text = "console.warn(\"" + breaking_text + "\");\n "
	placeholder_node = ParseTreeNode([], None)
	placeholder_node.parent = node_to_time
	node_to_time.child_list.insert( 0, placeholder_node)
	node_to_time.text.insert(0, [throws_text])
	return( 1)

def break_one_file( row, rnode, rmap, filename):
	to_break = row.to_move
	breaking_text = "TEMP_VAR_AUTOGEN_CALLING_" + str(row.name) + "__RANDOM"
	if break_stmt( rnode, rmap, to_break, breaking_text, filename) == 0:
		return(0)
	return(1)

def break_everything( dat, full_stmts, print_to_file = False, num_to_swap = -1):
	df = dat
	if num_to_swap != -1:
		df = pd.DataFrame.head( dat, n = num_to_swap)
	files = df.file.unique()
	for f in files:
		file = open(f, 'r')
		file_contents = file.read()
		file.close()
		if print_to_file:
			# save a copy of the file 
			save_old_copy(f, file_contents)
		file_contents = file_contents.split("\n")
		swaps = df[ df.file == f][['to_move', 'swap_before', 'swap_after']] # they'll already be sorted
		all_stmts = full_stmts[full_stmts.file == f]
		all_stmts.sort_values(['file','stmt'], inplace=True)
		# create the parse tree for this whole file
		(rnode, rmap) = convert__file_spec_stmt_list_to_tree( all_stmts.stmt.to_list(), file_contents)
		rnode.set_text( file_contents)
		add_swaps_to_all_stmt( all_stmts, swaps)
		swaps.apply( break_one_file, args=(rnode, rmap, f), axis=1)
		if print_to_file:
			file = open( f, 'w')
			file.write(ft.reduce( lambda a, b: a + "\n" + b, rnode.get_text(), "").lstrip())
			file.close()
		else:
			print("PROCESSING----------------------------------------------------")
			print(f)
			print("FILE CONTENTS BELOW-------------------------------------------")
			print_array_newline_sep(rnode.get_text())


def add_calls_timing( dat, full_stmts, print_to_file = False, num_to_swap = -1):
	df = dat
	if num_to_swap != -1:
		df = pd.DataFrame.head( dat, n = num_to_swap)
	files = df.call_file.unique()
	for f in files:
		file = open(f, 'r')
		file_contents = file.read()
		file.close()
		if print_to_file:
			# save a copy of the file 
			save_old_copy(f, file_contents)
		file_contents = file_contents.split("\n")
		calls = df[ df.call_file == f][['call_stmt', 'call_name']] # they'll already be sorted
		all_stmts = full_stmts[full_stmts.file == f]
		all_stmts.sort_values(['file','stmt'], inplace=True)
		# create the parse tree for this whole file
		(rnode, rmap) = convert__file_spec_stmt_list_to_tree( all_stmts.stmt.to_list(), file_contents)
		rnode.set_text( file_contents)
		calls['call_stmt'] = calls.apply( lambda row: all_stmts[all_stmts.stmt == row.call_stmt].stmt.to_list()[0], axis=1) 
		time_one_file( calls, rnode, rmap, f, do_time_call, [False]) # always add perf hooks when just timing a file
		if print_to_file:
			file = open( f, 'w')
			file.write(ft.reduce( lambda a, b: a + "\n" + b, rnode.get_text(), "").lstrip())
			file.close()
		else:
			print("PROCESSING----------------------------------------------------")
			print(f)
			print("FILE CONTENTS BELOW-------------------------------------------")
			print_array_newline_sep(rnode.get_text())

def do_swapping( dat, full_stmts, print_to_file = False, num_to_swap = -1, add_timing = False, pre_swap = True, post_swap = False, time_these_calls = None):
	# first, do all the timings in files which we don't also do swaps in
	if time_these_calls is not None:
		add_calls_timing( time_these_calls[ ~ time_these_calls.call_file.isin( dat.file)], full_stmts, print_to_file, -1) 
	df = dat
	if num_to_swap != -1:
		df = pd.DataFrame.head( dat, n = num_to_swap)
	files = df.file.unique()
	for f in files:
		file = open(f, 'r')
		file_contents = file.read()
		file.close()
		if print_to_file:
			# save a copy of the file 
			save_old_copy(f, file_contents)
		file_contents = file_contents.split("\n")
		swaps = df[ df.file == f][['to_move', 'swap_before', 'swap_after']] # they'll already be sorted
		# stmt_file_name = f[f.rindex("/") + 1 : -3] + "_stmts.txt" # the last "/" until the end is the root file name, then the -3 gets rid of the .ts or .js
		# all_stmts_data = pd.read_csv(stmt_file_name, sep = ',', header=None)
		# all_stmts = all_stmts_data.apply(convert_row_to_stmt, axis=1, result_type='expand')
		# all_stmts.columns = ['stmt', 'file']
		# all_stmts.sort_values(['file', 'stmt'], inplace=True)
		# reprocess_file_name( all_stmts)
		all_stmts = full_stmts[full_stmts.file == f]
		all_stmts.sort_values(['file','stmt'], inplace=True)
		# create the parse tree for this whole file
		(rnode, rmap) = convert__file_spec_stmt_list_to_tree( all_stmts.stmt.to_list(), file_contents)
		rnode.set_text( file_contents)
		add_swaps_to_all_stmt( all_stmts, swaps)
		perf_hooks_added = [False] # tracking whether or not we need to add perf_hooks to the file (once it's added once, don't add it again) -- it's an array for pass by ref 
		if pre_swap:
			file_sum = pd.DataFrame()
			if not post_swap: # only do the self-swaps if we're not post-swapping
				file_sum = deal_with_self_preswaps( swaps[swaps.to_move == swaps.swap_before], rnode, rmap, (add_timing and not post_swap), f)
			preswap_one_file( swaps[swaps.to_move != swaps.swap_before], rnode, rmap, (add_timing and not post_swap), f, (0 if file_sum.empty else file_sum.sum()), perf_hooks_added)
		if pre_swap and post_swap:
			swaps.swap_after = preprocess_df_both_reorders( swaps)
		if post_swap: # implies not preswap
			deal_with_self_postswaps( swaps[swaps.to_move == swaps.swap_after], rnode, rmap, add_timing, f, perf_hooks_added)
			lateswap_one_file( swaps[swaps.to_move != swaps.swap_after], rnode, rmap, add_timing, f, perf_hooks_added)
		if time_these_calls is not None:
			calls = time_these_calls[ time_these_calls.call_file == f][['call_stmt', 'call_name']]
			calls['call_stmt'] = calls.apply( lambda row: all_stmts[all_stmts.stmt == row.call_stmt].stmt.to_list()[0], axis=1) 
			time_one_file( calls, rnode, rmap, f, do_time_call, perf_hooks_added)
		if print_to_file:
			file = open( f, 'w')
			file.write(ft.reduce( lambda a, b: join_stmts(a, b), rnode.get_text(), "").lstrip())
			file.close()
		else:
			print("PROCESSING----------------------------------------------------")
			print(f)
			print("FILE CONTENTS BELOW-------------------------------------------")
			print_array_newline_sep(rnode.get_text())

def do_self_swap( row, rnode, rmap, add_timing = False, filename = ""):
	to_move = row.to_move
	temp_var_name = "TEMP_VAR_AUTOGEN" + str(row.name) + "__RANDOM"
	# these should be the same stmts, since we should only have one DF
	# probably make a column in our DF that is "swap_before", and then run through the ones with values
	# move_stmt( rnode, rmap, to_move, move_before)
	if not add_timing:
		if split_single_await( rnode, rmap, to_move, temp_var_name, add_timing, filename) == 0:
			return(0)
	else:
		if time_await( rnode, rmap, to_move, temp_var_name, filename) == 0:
			return(0)
	return(1)


def deal_with_self_preswaps( self_swaps, rnode, rmap, add_timing = False, filename = ""):
	# don't need to do any recursive checking, since this is all going to be self-swaps
	# all we need to do is split the await, basically the same work as if we were just adding timing
	to_ret = self_swaps.apply( do_self_swap, args=(rnode, rmap, add_timing, filename), axis=1)
	if to_ret is not None:
		return( to_ret)
	return( pd.DataFrame())

# need to split an await statement even if it cant be swapped any earlier, since when we move it 
# later the promise creation needs to stay where it was originally
def split_single_await( root_node, root_map, stmt_to_split, temp_var_name, add_timing = False, filename = ""):
	node_to_split = root_map[stmt_to_split]
	# all we care about here is the await, we;re just updating the text 
	(text_ind, ind_to_split_at) = get_index_with_await(node_to_split.text)
	(front_paren_stack, end_paren_stack) = get_compensating_parens( node_to_split.text, text_ind, ind_to_split_at)
	if ind_to_split_at == -1 or front_paren_stack == -1: # then this is a problem, and we just won't do the reordering
		print("There's an issue and we can't automatically split the following statement: ")
		node_to_split.print()
		print("DONE REPORTING PROBLEMS")
		return( 0)
	# split both the text array and the child_list
	start_text = node_to_split.text[text_ind][0 : ind_to_split_at]
	end_text = node_to_split.text[text_ind][ ind_to_split_at + 1 : ]
	# get the text we're going to split: 
	split_text = node_to_split.text[text_ind][ind_to_split_at]
	# adapted from the time_await code, it's basically the same thing but we're not adding timing
	# we're just splitting the await
	new_await_var = "var " + temp_var_name + " = await " + front_paren_stack + split_text[ split_text.index('await') + len('await') : ]
	string_before_await = split_text[0: split_text.index('await')] + " " + temp_var_name
	# if build_paren_stack(string_before_await) != "": # the addition of the varname doesnt change this funcionality
	# 	# don't even split the text any more
	# 	node_to_split.text = [[timing_pre_text]+ node_to_split.text[text_ind] + ["\n" + timing_post_text]]
	# else:
	node_to_split.text = [start_text + [new_await_var]+ end_text + [end_paren_stack + string_before_await]]
	placeholder_node = ParseTreeNode([], None)
	placeholder_node.parent = node_to_split
	node_to_split.child_list.insert( ind_to_split_at, placeholder_node)
	return( 1)	

def deal_with_self_postswaps( self_swaps, rnode, rmap, add_timing = False, filename = "", perf_hooks_added = [False]):
	# don't need to do any recursive checking, since this is all going to be self-swaps
	# all we need to do is split the await, basically the same work as if we were just adding timing
	if add_timing:
		results = self_swaps.apply( do_time, args=(rnode, rmap, filename), axis=1)
		if not results.empty and results.sum() > 0 and not perf_hooks_added[0]:
			req_perf_node = ParseTreeNode( [], None)
			req_perf_node.parent = rnode
			req_perf_node.text = [["const perf_hooks = require(\'perf_hooks\'); "]]
			ind_to_insert = 0
			if len(rnode.text) > 0 and len(rnode.text[0]) > 0 and len(rnode.text[0][0]) > 1 and rnode.text[0][0][0:2] == "#!": # cant move above #! command
				ind_to_insert = 1
			rnode.child_list.insert(ind_to_insert, req_perf_node)
			rnode.text.insert(ind_to_insert, [""])
			# update to say we've adding perf_hooks to this file, and therefore don't need to do it again
			perf_hooks_added[0] = True 


# replace the root of a string with a new specified root
# throw an exception if the string does not have the root old_root
def change_string_root( row, org_root, new_root, is_call = False):
	org_string = ""
	if not is_call:
		org_string = row.file
	else:
		org_string = row.call_file
	if org_string.index(org_root) != 0:
		raise ValueError("The original path " + org_string + " does not have the original root: " + org_root)
	return( new_root + org_string[ len(org_root): ]) 


def add_swaps_to_all_stmt( all_stmts, swap_df):
	# since the rmap is indexed by statement object, and we've created the swap_associations and all_stmts dataframes
	# separately, we can't index the rmap with the swap_associations
	# so, we need to add a column to all_stmts, with the corresponding association but with the right objects
	try:
		swap_df['to_move'] = swap_df.apply( lambda row: all_stmts[all_stmts.stmt == row.to_move].stmt.to_list()[0], axis=1) # can index at 0 since there will only be one
		swap_df['swap_before'] = swap_df.apply( lambda row: all_stmts[all_stmts.stmt == row.swap_before].stmt.to_list()[0], axis=1)
		swap_df['swap_after'] = swap_df.apply( lambda row: all_stmts[all_stmts.stmt == row.swap_after].stmt.to_list()[0], axis=1)
	except IndexError:
		print(swap_df)

def do_early_swap( row, rnode, rmap, add_timing = False, filename = ""):
	to_move = row.to_move
	move_before = row.swap_before
	temp_var_name = "TEMP_VAR_AUTOGEN" + str(row.name) + "__RANDOM"
	# these should be the same stmts, since we should only have one DF
	# probably make a column in our DF that is "swap_before", and then run through the ones with values
	# move_stmt( rnode, rmap, to_move, move_before)
	print(row)
	if move_and_split_await( rnode, rmap, to_move, move_before, temp_var_name, add_timing, filename) == 0:
		return(0)
	return(1)

def do_late_swap( row, rnode, rmap, add_timing = False, filename = ""):
	to_move = row.to_move
	move_after = row.swap_after
	temp_var_name = "TEMP_VAR_AUTOGEN" + str(row.name) + "__RANDOM"
	# these should be the same stmts, since we should only have one DF
	# probably make a column in our DF that is "swap_before", and then run through the ones with values
	# move_stmt( rnode, rmap, to_move, move_before)
	if move_await_later( rnode, rmap, to_move, move_after, temp_var_name, add_timing, filename) == 0:
		return(0)
	return(1)

def do_time( row, rnode, rmap, filename):
	to_time = row.to_move
	temp_var_name = "TEMP_VAR_AUTOGEN" + str(row.name) + "__RANDOM"
	if time_await( rnode, rmap, to_time, temp_var_name, filename) == 0:
		return(0)
	return(1)

def do_time_call( row, rnode, rmap, filename):
	to_time = row.call_stmt
	temp_var_name = "TEMP_VAR_AUTOGEN_CALLING_" + str(row.name) + "_" + row.call_name + "__RANDOM"
	if time_call( rnode, rmap, to_time, temp_var_name, filename) == 0:
		return(0)
	return(1)

# function to preprocess a dataframe of swaps for ONE FILE
# if we're doing both forward and backward swapping, there's no guarantee that 
# a statement can swap down to something below where another statement is swapping up
# and, since there is no dependency check between these statements, we need to conservatively
# assume that there is a dependency
# solution: set the swap_after to be the min of swap_after and the swap_befores of any stmts 
# which themselves are > current statement and their swap_befores are > current_stmt
def preprocess_df_both_reorders( swap_df):
	# for each statement
	return(swap_df.apply( get_late_swap_for_row, args=( swap_df, ), axis=1))

def get_late_swap_for_row( row, df):
	to_consider = df[(df.to_move > row.swap_after) & (df.swap_before > row.to_move)]
	if to_consider.empty:
		return( row.swap_after)
	earliest_later_up = to_consider.swap_before.min()
	return( min( row.swap_after, earliest_later_up))

def swap_condition( results, tsum):
	if results.empty and tsum > 0:
		return True
	elif results.empty:
		return False
	elif results.sum() > 0:
		return True 
	return False

def preswap_one_file( swap_df, rnode, rmap, add_timing = False, filename = "", tsum = 0, perf_hooks_added=[False], counter=0):
	recursive_swaps = swap_df[swap_df.swap_before.isin(swap_df.to_move)]
	if not recursive_swaps.empty:
		preswap_one_file( recursive_swaps, rnode, rmap, add_timing, filename, tsum, perf_hooks_added, counter + 1)
		swap_df = pd.concat([recursive_swaps, swap_df]).drop_duplicates(keep=False)
	results = swap_df.apply( do_early_swap, args=(rnode, rmap, add_timing, filename), axis=1)
	# dont need to time anymore since timing will be adding during post-swap
	if add_timing and counter == 0 and swap_condition(results, tsum) and not perf_hooks_added[0]: 
		req_perf_node = ParseTreeNode( [], None)
		req_perf_node.parent = rnode
		req_perf_node.text = [["const perf_hooks = require(\'perf_hooks\'); "]]
		ind_to_insert = 0
		if len(rnode.text) > 0 and len(rnode.text[0]) > 0 and len(rnode.text[0][0]) > 1 and rnode.text[0][0][0:2] == "#!":
			ind_to_insert = 1
		rnode.child_list.insert(ind_to_insert, req_perf_node)
		rnode.text.insert(ind_to_insert, [""])
		# update to say we've adding perf_hooks to this file, and therefore don't need to do it again
		perf_hooks_added[0] = True 
		# don't add it to the rmap since it doesnt really have a corresponding statement

def lateswap_one_file( swap_df, rnode, rmap, add_timing = False, filename = "", perf_hooks_added = [False], counter=0):
	recursive_swaps = swap_df[swap_df.swap_after.isin(swap_df.to_move)]
	if not recursive_swaps.empty:
		lateswap_one_file( recursive_swaps, rnode, rmap, add_timing, filename, perf_hooks_added, counter + 1)
		swap_df = pd.concat([recursive_swaps, swap_df]).drop_duplicates(keep=False)
	results = swap_df.apply( do_late_swap, args=(rnode, rmap, add_timing, filename), axis=1)
	if add_timing and counter == 0 and (results.empty or results.sum() > 0) and not perf_hooks_added[0]: 
		req_perf_node = ParseTreeNode( [], None)
		req_perf_node.parent = rnode
		req_perf_node.text = [["const perf_hooks = require(\'perf_hooks\'); "]]
		ind_to_insert = 0
		if len(rnode.text) > 0 and len(rnode.text[0]) > 0 and len(rnode.text[0][0]) > 1 and rnode.text[0][0][0:2] == "#!":
			ind_to_insert = 1
		rnode.child_list.insert(ind_to_insert, req_perf_node)
		rnode.text.insert(ind_to_insert, [""])
		perf_hooks_added[0] = True

def time_one_file( swap_df, rnode, rmap, filename, timing_func = do_time, perf_hooks_added = [False]):
	results = swap_df.apply( timing_func, args=(rnode, rmap, filename), axis=1)
	if not results.empty and results.sum() > 0 and not perf_hooks_added[0]:
		req_perf_node = ParseTreeNode( [], None)
		req_perf_node.parent = rnode
		req_perf_node.text = [["const perf_hooks = require(\'perf_hooks\'); "]]
		ind_to_insert = 0
		if len(rnode.text) > 0 and len(rnode.text[0]) > 0 and len(rnode.text[0][0]) > 1 and rnode.text[0][0][0:2] == "#!":
			ind_to_insert = 1
		rnode.child_list.insert(ind_to_insert, req_perf_node)
		rnode.text.insert(ind_to_insert, [""])
		perf_hooks_added[0] = True
		# don't add it to the rmap since it doesnt really have a corresponding statements


def join_stmts(a, b):
	if b.lstrip(" ").lstrip("\t").split(" ")[0] == "as":
		return( a + " " + b)
	return( a + "\n" + b)

def print_rnode_to_file( filename, rnode):
	f = open(filename, 'w')
	f.write(ft.reduce( lambda a, b: join_stmts(a, b), rnode.get_text(), ""))
	f.close()

def main_example():
	
	org_root = "/home/ellen/Documents/odasa/projects/kactus/revision-2020-January-06--15-50-46/src"
	new_root = "/home/ellen/Documents/ASJProj/TESTING_reordering/kactus"
	org_root = new_root + "_analyzeMe"

	# now, full_stmts includes all statements in all files to add timings to, which could include the files that have calls which depend
	# on the awaits we've reordered, depending on what mode the analysis is in
	full_stmts = pd.read_csv("allStmts.csv", sep = ',', header=None)
	full_stmts = full_stmts.apply(convert_row_to_stmt, axis=1, result_type='expand')
	full_stmts.columns = ['stmt', 'file']
	# full_stmts['stmt'] = full_stmts.apply( convert_string_to_stmt, axis=1)
	full_stmts['file'] = full_stmts.apply( change_string_root, args=(org_root, new_root), axis=1)
	full_stmts.sort_values(['file'], inplace=True) # probably don't even need to do this

	data = pd.read_csv("swaps.csv", sep = ',', header=None)
	output = data.apply(convert_row_to_stmts, axis=1, result_type='expand')
	output.columns = ['to_move', 'swap_before', 'swap_after', 'file']
	output.drop( output[(output.to_move == output.swap_before) & (output.to_move == output.swap_after)].index, inplace=True) # delete rows that mean no swapping

	output['keep_stmt'] = output.apply(lambda x: output.apply( keep_first_stmt, args=(x.to_move, x.file), axis=1).all(), axis=1)	
	output.drop_duplicates(inplace=True) # delete duplicate rows
	output = output[output.keep_stmt]    # delete overlapping rows
	# this is open to change, but right now sort by files first (to group everything by file),
	# then, for everything in the same file swap by swap_before
	# then, finally, sort by to_move
	# we can sort by to_move since we've defined custom == and < for Stmts
	output.sort_values(['file', 'swap_before', 'to_move'], inplace=True)
	output['file'] = output.apply( change_string_root, args=(org_root, new_root), axis=1)

	output.drop([664], inplace=True)
	print_to_file = True
	num_to_swap = -1
	add_timing = True
	do_swapping( output, full_stmts, print_to_file, num_to_swap, add_timing, True, False)
	do_swapping( output, full_stmts, print_to_file, num_to_swap, add_timing, False, True)
	do_swapping( output, full_stmts, print_to_file, num_to_swap, add_timing, True, True)
	just_add_timing( output, full_stmts, print_to_file, num_to_swap)


	data = pd.read_csv("time_calls.csv", sep = ',', header=None)
	calls_output = data.apply(convert_row_to_stmts_with_calls, axis=1, result_type='expand')
	calls_output.columns = ['to_move', 'swap_before', 'swap_after', 'file', 'call_stmt', 'call_name', 'call_file']
	calls_output.drop( calls_output[(calls_output.to_move == calls_output.swap_before) & (calls_output.to_move == calls_output.swap_after)].index, inplace=True) # delete rows that mean no swapping
	# get rid of statements overlapping
	calls_output['keep_stmt'] = calls_output.apply(lambda x: calls_output.apply( keep_first_stmt, args=(x.to_move, x.call_file), axis=1).all(), axis=1)	
	calls_output.drop_duplicates(inplace=True) # delete duplicate rows
	calls_output = calls_output[calls_output.keep_stmt]    # delete overlapping rows
	# don't bother sorting
	calls_output = calls_output[['call_stmt', 'call_name', 'call_file']].drop_duplicates()
	calls_output = calls_output[ calls_output.call_stmt != Stmt(-2, -2, -2, -1)] # get rid of the garbage placeholders
	calls_output['call_file'] = calls_output.apply( change_string_root, args=(org_root, new_root, True), axis=1)

	add_calls_timing( calls_output, full_stmts, print_to_file, num_to_swap)

	do_swapping(output, full_stmts, True, -1, True, True, True, calls_output)


	# useful for debugging:
	f = all_stmts.file[0]
	file = open(f, 'r')
	file_contents = file.read()
	file_contents = file_contents.split("\n")
	file.close()

	all_stmts = full_stmts[full_stmts.file == f]

	(rnode, rmap) = convert__file_spec_stmt_list_to_tree( all_stmts.stmt.to_list(), file_contents)
	rnode.set_text( file_contents)

# main()

# actually do the reordering to project specified
if len(sys.argv) < 3:
	print("Usage: python reorder_me.py original_source_dir output_dir [transformation_mode]")
	sys.exit()


new_root = sys.argv[2]
org_root = sys.argv[1]

transformation_mode = "reordering" if len(sys.argv) == 3 else sys.argv[3]


# now, full_stmts includes all statements in all files to add timings to, which could include the files that have calls which depend
# on the awaits we've reordered, depending on what mode the analysis is in
full_stmts = pd.read_csv("allStmts.csv", sep = ',', header=None)
full_stmts = full_stmts.apply(convert_row_to_stmt, axis=1, result_type='expand')
full_stmts.columns = ['stmt', 'file']
# full_stmts['stmt'] = full_stmts.apply( convert_string_to_stmt, axis=1)
full_stmts['file'] = full_stmts.apply( change_string_root, args=(org_root, new_root), axis=1)
full_stmts.sort_values(['file'], inplace=True) # probably don't even need to do this

data = pd.read_csv("swaps.csv", sep = ',', header=None)
output = data.apply(convert_row_to_stmts, axis=1, result_type='expand')
output.columns = ['to_move', 'swap_before', 'swap_after', 'file']
output.drop( output[(output.to_move == output.swap_before) & (output.to_move == output.swap_after)].index, inplace=True) # delete rows that mean no swapping

output['keep_stmt'] = output.apply(lambda x: output.apply( keep_first_stmt, args=(x.to_move, x.file), axis=1).all(), axis=1)	
output.drop_duplicates(inplace=True) # delete duplicate rows
output = output[output.keep_stmt]    # delete overlapping rows
# this is open to change, but right now sort by files first (to group everything by file),
# then, for everything in the same file swap by swap_before
# then, finally, sort by to_move
# we can sort by to_move since we've defined custom == and < for Stmts
output.sort_values(['file', 'swap_before', 'to_move'], inplace=True)
output['file'] = output.apply( change_string_root, args=(org_root, new_root), axis=1)

print_to_file = True
num_to_swap = -1 # do all the reorderings
add_timing = True # True if you want to time each await

if transformation_mode == "reordering":
	# the 2 "True" arguments at the end indicate that we're both moving promise creation and the await itself
	do_swapping( output, full_stmts, print_to_file, num_to_swap, add_timing, True, True)
elif transformation_mode == "just_timing":
	just_add_timing( output, full_stmts, print_to_file, num_to_swap)
elif transformation_mode == "track_affected_tests":
	break_everything( output, full_stmts, print_to_file, num_to_swap)
else:
	print("Invalid transformation mode specified, exiting now")
	sys.exit()