"""F: A string which is an S-expression of a PC formula. You can assume:
The operators used are IF,IFF,AND,OR,and NOT. 
All operators (except for NOT) have two arguments
All propositional symbols will be lower-case alphanumberic strings
All formulae are well-formed (UNDERGRADUATE STUDENTS ONLY)

Returns either a string or integer: 
“E” – If the formula was not well-formed (GRADUATE STUDENTS ONLY)
“T” – If the formula is a tautology,
“U” – If the formula is unsatisfiable, else:
i – An integer showing the number of rows that are satisfiable
"""

import re
from itertools import product

"""
	Define operator functions
	They take as input boolean variables and output the truth value
"""
def AND(atom1, atom2):
	if (atom1 and atom2) == True:
		return True
	else:
		return False

def OR(atom1, atom2):
	if atom1 or atom2:
		return True
	else:
		return False

def NOT(atom1):
	return (not atom1)

# also called implies
def IF(atom1, atom2):
	if atom1 == atom2:
		return True
	elif atom2 == False:
		return False
	else:
		return True

def IFF(atom1, atom2):
	if atom1 == atom2:
		return True
	else:
		return False

# Store the operations in a dict to make accessing them from a string easy
global function_map
function_map = {
	'AND':AND,
	'OR':OR,
	'NOT':NOT,
	'IF':IF,
	'IFF':IFF
}


# define valid operators and valid symbols
symbol_re = re.compile(r'([a-z0-9])+')
valid_symbols = ['(',')','IF','IFF','AND','OR','NOT']
operators = ['IF', 'IFF', 'AND', 'OR', "NOT"]
two_ary_operators = ['IF', 'IFF', 'AND', 'OR']

def proveFormula(F):
	# Each atom is hashed and stored in a dict
	# The string is the key and the value is the current assignment of True or False
	global atom_map
	atom_map = {}
	# Step 1, check that the formulae is well formed
	f_tokens = preProcess(F)
	if f_tokens == 'E':
		return 'E'
	
	f_tree = buildTree(f_tokens)
	total_table_values = 0
	total_true_table_values = 0
	all_assignments = list(product([True, False], repeat=len(atom_map)))
	# enumerate over all entries in truth table
	for assignment in all_assignments:
		# set values of atoms for this iterations
		for i,(k,v) in enumerate(atom_map.items()):
			atom_map[k] = assignment[i]
		
		# call solveTheorem(f_tree) to get the value of this entry in the table
		result = solveTheorem(f_tree)
		if result == True:
			total_true_table_values += 1
		total_table_values += 1
	
	# finally, check the result and return appropriate value
	if total_table_values == total_true_table_values:
		return 'T'
	elif total_true_table_values == 0:
		return 'U'
	else:
		return total_true_table_values


"""
	Given the input formula, process and check for wff
	If the formula is not well formed, return E
	Rules of a WFF:
		1. A single atom is valid, for instance "p"
		2. Multiple atoms not joined by an operator is invalid, for instance "p p"
		3. A 2-ary operator must be followed by 2 atoms and be in paranthesis, for instance "(AND p p)" not "AND p p" or "AND p" or "AND p p p p" or "(AND)"
		4. A 1-ary operator must be followed by 1 atom and be in paranthesis, for instance "(NOT p)" not "NOT p" or "NOT p p" or "(NOT)"
		5. Paranthesis must be closed, for instance "(NOT p)" not "(NOT p" or "NOT p)"
		6. Paranthesis can't be empty, for instance "()" is invalid
		7. Closing paranthesis can't preceede an opening one, for instance "))(("
		8. There must ONLY be valid characters, otherwise reject immedietly, for istance "(NOT p) >< $" is invalid
		9. Empty strings are not well formed
"""
# Make sure paranthesis match
def checkParanthesis(F_tokens):
    all_paranthesis = []
    for token in F_tokens:
        if token not in ["(", ")"]:
            continue    # skip over anything that isn't paranthesis 
        if token == '(':
            all_paranthesis.append('(')
        elif token == ')':
            if not all_paranthesis:
                return False    # handle case where ) comes before a ( first 
                    
            curr_token = all_paranthesis.pop()

    # finally make sure it is balanced at the end
	# there should be no characters in the stack
    if all_paranthesis:
        return False
    else:
        return True



def preProcess(F):
    # First tokenize the input
	F_tokens = []
	F = re.sub(r'\(', ' ( ', F)
	F = re.sub(r'\)', ' ) ', F)
	F_tokens = F.split()
	if len(F_tokens) == 0:
		return 'E'
    # Check for balanced paranthesis
	if not checkParanthesis(F_tokens):
		return 'E'	# cases 5 and 7

	# Check for garbage characters
	for token_i,token in enumerate(F_tokens):
		# Check that operators have the correct number of operands
		if token in operators:
			if token == 'NOT':
				try:
					if F_tokens[token_i + 1] != '(' and re.fullmatch(symbol_re, F_tokens[token_i + 1]) is None:
						return 'E'
				except IndexError:
					# handle case where the operator is the last character in the list
					return 'E'

				continue
			elif token in ['AND', 'OR', 'NOT', 'IF', 'IFF']:
				# check the first operand
				try:
					if F_tokens[token_i + 1] != '(' and re.fullmatch(symbol_re, F_tokens[token_i + 1]) is None:
						return 'E'
				except IndexError:
					# handle case where the operator is the last character in the list
					return 'E'
				
				# now check the second operand
				if re.fullmatch(symbol_re, F_tokens[token_i + 1]) is not None:
					try:
						if F_tokens[token_i + 2] != '(' and re.fullmatch(symbol_re, F_tokens[token_i + 2]) is None:
							return 'E'
					except IndexError:
						return 'E'
				
				if F_tokens[token_i + 1] == '(':
					# locate the end of the current block and check the second operand
					try:
						if F_tokens[token_i + 2] == ')':
							return 'E'  # empty paranthesis
						# find the number of ( so we can locate the correct ) to go back to
						ptr = token_i + 2
						all_paranthesis = ['(']
						while len(all_paranthesis) != 0:
							if F_tokens[ptr] not in ["(", ")"]:
								ptr += 1
								continue    # skip over anything that isn't paranthesis 
							if F_tokens[ptr] == '(':
								all_paranthesis.append('(')
										
							if F_tokens[ptr] == ')':
								all_paranthesis.pop()
							
							ptr += 1
						if F_tokens[ptr] != '(' and re.fullmatch(symbol_re, F_tokens[ptr]) is None:
							return 'E'
					except IndexError:
						return 'E'   

			continue    # valid operator
		# check for empty paranthesis
		elif token == '(' and F_tokens[token_i + 1] == ')':
			return 'E'
		# check for atoms inside paranthesis without operator
		elif token == '(' and F_tokens[token_i + 1] not in operators:
			return 'E'
		elif re.fullmatch(symbol_re, token) is not None:
			# finally check for invalid atoms, atoms not part of operator
			if len(F_tokens) == 1:
				continue # a single atom is valid
			try:
				# an atom is at most 2 indexes away from an operator
				if F_tokens[token_i - 1] not in operators and F_tokens[token_i - 2] not in two_ary_operators:
					if F_tokens[token_i - 1] == ')':
						# find the number of ) so we can locate the correct ( to go back to
						ptr = token_i - 1
						num_paren = 0
						while(F_tokens[ptr] == ')'):
							ptr -= 1
							num_paren += 1
						# now go to the correct index and check that it is an operator
						prev_paren = [i for i,n in enumerate(F_tokens[:token_i][::-1]) if n == '('][num_paren]
						if F_tokens[token_i - prev_paren] not in operators:
							return 'E'
					else:
						return 'E'
				else:
					continue
			except IndexError:
				return 'E'

			continue    # valid atom
		elif token == ')':
			# don't need to do anything special for closing paranthesis
			continue
		# finally handle garbage characters
		elif token not in valid_symbols and re.fullmatch(symbol_re, token) is None:
			return 'E'

	return F_tokens


"""
	Create binary tree to represent S-expression
	Expects that the formula has been determined to be wff
	Input:
		F_tokens: The tokenized S-expression
		F_tree: A list used to recursively build the tree
"""
def buildTree(F_tokens):
	token = F_tokens[0]
	sublist = []
	if token == '(':
		# locate the last )
		# should only step in here for the first set of ()
		ind = len(F_tokens)
		return buildTree(F_tokens[1:ind-1])
	if token in two_ary_operators:
		sublist.append(F_tokens[0])
		# find the left and right sub S-expressions to recurse on
		# if their just single atoms, append to list left to right
		if F_tokens[1] == '(':
			paren_stack = []
			i = 0
			for i,token in enumerate(F_tokens):
				if token not in ["(", ")"]:
					continue    # skip over anything that isn't paranthesis 
				if token == '(':
					paren_stack.append('(')
				if token == ')':
					# we've found the child S-expression
					paren_stack.pop()
					if len(paren_stack) == 0:
						break			
					
			
			sublist.append(buildTree(F_tokens[2:i]))
			# now solve the right child
			if F_tokens[i+1] == '(':
				# both the left and the right child are defined recursively
				paren_stack = []
				j = 0
				for j,token in enumerate(F_tokens):
					if token not in ["(", ")"]:
						continue    # skip over anything that isn't paranthesis 
					if token == '(':
						paren_stack.append('(')
					if token == ')':
						# we've found the child S-expression
						if len(paren_stack) == 0:
							break			
						paren_stack.pop()

				sublist.append(buildTree(F_tokens[i+2:j]))
			else:
				# register the atom into the symbol table
				atom_map[F_tokens[i+1]] = True
				sublist.append(F_tokens[i+1])
		# the left child is a base case
		else:
			atom_map[F_tokens[1]] = True
			sublist.append(F_tokens[1])
			# but the right child may need to be recursed on
			if F_tokens[2] == '(':
				paren_stack = []
				i = 0
				for i,token in enumerate(F_tokens):
					if token not in ["(", ")"]:
						continue    # skip over anything that isn't paranthesis 
					if token == '(':
						paren_stack.append('(')
					if token == ')':
						# we've found the child S-expression
						if len(paren_stack) == 0:
							break			
						paren_stack.pop()
			
				sublist.append(buildTree(F_tokens[3:i]))
			else:
				atom_map[F_tokens[2]] = True
				sublist.append(F_tokens[2])

	# only need to handle the left child
	if F_tokens[0] == 'NOT':
		sublist.append(F_tokens[0])
		if F_tokens[1] == '(':
			paren_stack = []
			i = 0
			for i,token in enumerate(F_tokens):
				if token not in ["(", ")"]:
					continue    # skip over anything that isn't paranthesis 
				if token == '(':
					paren_stack.append('(')
				if token == ')':
					# we've found the child S-expression
					if len(paren_stack) == 0:
						break			
					paren_stack.pop()
			
			sublist.append(buildTree(F_tokens[2:i]))
		else:
			atom_map[F_tokens[1]] = True
			sublist.append(F_tokens[1])
	
	# finally handle the base case of a single atom
	if re.fullmatch(symbol_re, F_tokens[0]) is not None:
		atom_map[F_tokens[0]] = True
		sublist.append(F_tokens[0])

	return sublist

"""
	Recursively solve for the value of the ith table position
	Input:
		F_tree: the parsed S-expression
"""
def solveTheorem(F_tree):
	#	1. lookup the operator at this level of the list
	#		or if it's just a single atom, return the current value
	#	2. call the operator, passing the arguments
	#		if 1 of the args is a list, recursively solve that S-expression
	# base case, just return the current assignment of the atom
	if len(F_tree) == 1:
		return atom_map[F_tree[0]]
	if F_tree in list(atom_map.keys()):
		return atom_map[F_tree]
	# otherwise return the result of the operator applied to the sub S-expressions
	else:
		if F_tree[0] in two_ary_operators:
			return function_map[F_tree[0]](solveTheorem(F_tree[1]), solveTheorem(F_tree[2]))
		else:
			# NOT has only 1 argument
			return NOT(solveTheorem(F_tree[1]))