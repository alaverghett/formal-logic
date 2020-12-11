"""
    CAP 6632 Extra Credit
    Antonio Laverghetta Jr.
"""

import re
import time


# Given an S-expression, return whether the formulae is satisfiable
def isSatisfiable(F):
    # Build syntax tree, one for each formula
    F_expressions = []
    start_time = time.time()

    objects = []
    for f in F:
        f_exp = parseExpression(f)
        F_expressions.append(f_exp)

    # run Tableaux to prove sat or unsat
    return tableaux(F_expressions, start_time)


def tableaux(F_expressions, start_time):
    # in the tableaux, each formula is a node in a tree
    # a node contains the formula
    # a flag to indicate whether the formula has been applied
    # a pointer to the parent
    # a list of pointers to the children (in order of traversal)
    # the root node (the formula we are passed) has a parent pointer of null
    # likewise, the children are null initially and are added as we build the tree

    class Node():
        def __init__(self, formula, parent, children, world,opensWorld=False):
            self.formula = formula
            self.parent = parent
            self.children = children
            self.isApplied = False  # True means the node is closed
            # for modal logic, we also need to represent the world we are currently in
            self.world = world
            # for nodes that create a new world, use this as a special flag to check them
            self.opensWorld = opensWorld
    
    # the tableaux is simply a list of nodes for easy traversal
    tableaux = []

    # for modal logic, indicates all world that have been created
    # also indicates the number of the most recently created world
    # increments whenever a new world is created
    global total_worlds
    total_worlds = 0
    
    def NOTNOT(node,open_children,world):
        # strip out double negative
        arg = node.formula[1][1]
        for child in open_children:
            new_child = Node(formula=arg,parent=child,children=[],world=world)
            tableaux.append(new_child)
            child.children.append(new_child)
    
    def IF(node,open_children,world):
        # create the children
        left_arg = ['NOT',node.formula[1]]

        right_arg = node.formula[2]
        # append to every open branch
        for child in open_children:
            left_child = Node(formula=left_arg,parent=child,children=[],world=world)
            right_child = Node(formula=right_arg,parent=child,children=[],world=world)
            tableaux.append(left_child)
            tableaux.append(right_child)
            child.children.append(left_child)
            child.children.append(right_child)


    def IFF(node,open_children,world):
        # create the children
        left_normal = node.formula[1]
        left_negated = ['NOT', node.formula[1]]
        right_normal = node.formula[2]
        right_negated = ['NOT',node.formula[2]]

        for child in open_children:
            # first the left branch
            left_child = Node(formula=left_normal,parent=child,children=[],world=world)
            child.children.append(left_child)
            left_grandchild = Node(formula=right_normal,parent=left_child,children=[],world=world)
            left_child.children.append(left_grandchild)

            # then the right
            right_child = Node(formula=left_negated,parent=child,children=[],world=world)
            child.children.append(right_child)
            right_grandchild = Node(formula=right_negated,parent=right_child,children=[],world=world)
            right_child.children.append(right_grandchild)

            # add all nodes inorder
            tableaux.append(left_child)
            tableaux.append(left_grandchild)
            tableaux.append(right_child)
            tableaux.append(right_grandchild)

    def XOR(node,open_children,world):
        # create the children
        left_normal = node.formula[1]
        left_negated = ['NOT', node.formula[1]]
        right_normal = node.formula[2]
        right_negated = ['NOT',node.formula[2]]

        for child in open_children:
            # first the left branch
            left_child = Node(formula=left_negated,parent=child,children=[],world=world)
            child.children.append(left_child)
            left_grandchild = Node(formula=right_normal,parent=left_child,children=[],world=world)
            left_child.children.append(left_grandchild)

            # then the right
            right_child = Node(formula=left_normal,parent=child,children=[],world=world)
            child.children.append(right_child)
            right_grandchild = Node(formula=right_negated,parent=right_child,children=[],world=world)
            right_child.children.append(right_grandchild)

            # add all nodes inorder
            tableaux.append(left_child)
            tableaux.append(left_grandchild)
            tableaux.append(right_child)
            tableaux.append(right_grandchild)

    def AND(node,open_children,world):
        # get the args of and
        args = node.formula[1:]
        for child in open_children:
            parent = child
            for arg in args:
                # create a new node and append it to the tableaux
                new_node = Node(formula=arg,parent=parent,children=[],world=world)
                tableaux.append(new_node)
                parent.children.append(new_node)
                parent = new_node

    def OR(node,open_children,world):
        args = node.formula[1:]
        for child in open_children:
            for arg in args:
                new_node = Node(formula=arg,parent=child,children=[],world=world)
                child.children.append(new_node)
                tableaux.append(new_node)

    def NOTAND(node,open_children,world):
        args = node.formula[1][1:]
        # negate the args
        args = [['NOT',arg] for arg in args]

        for child in open_children:
            for arg in args:
                new_node = Node(formula=arg,parent=child,children=[],world=world)
                child.children.append(new_node)
                tableaux.append(new_node)

    def NOTOR(node,open_children,world):
        # get the args of and
        args = node.formula[1][1:]
        # negate the args
        args = [['NOT',arg] for arg in args]

        for child in open_children:
            parent = child
            for arg in args:
                # create a new node and append it to the tableaux
                new_node = Node(formula=arg,parent=parent,children=[],world=world)
                tableaux.append(new_node)
                parent.children.append(new_node)
                parent = new_node

    def NOTIF(node,open_children,world):
        left_child = node.formula[1][1]
        right_child = ['NOT', node.formula[1][2]]
        
        for child in open_children:
            new_node = Node(formula=left_child,parent=child,children=[],world=world)
            child.children.append(new_node)
            new_node_child = Node(formula=right_child,parent=new_node,children=[],world=world)
            new_node.children.append(new_node_child)

            tableaux.append(new_node)
            tableaux.append(new_node_child)

    def NOTIFF(node,open_children,world):
        # create the children
        left_normal = node.formula[1][1]
        left_negated = ['NOT', node.formula[1][1]]
        right_normal = node.formula[1][2]
        right_negated = ['NOT',node.formula[1][2]]

        for child in open_children:
            # first the left branch
            left_child = Node(formula=left_normal,parent=child,children=[],world=world)
            child.children.append(left_child)
            left_grandchild = Node(formula=right_negated,parent=left_child,children=[],world=world)
            left_child.children.append(left_grandchild)

            # then the right
            right_child = Node(formula=left_negated,parent=child,children=[],world=world)
            child.children.append(right_child)
            right_grandchild = Node(formula=right_normal,parent=right_child,children=[],world=world)
            right_child.children.append(right_grandchild)

            # add all nodes inorder
            tableaux.append(left_child)
            tableaux.append(left_grandchild)
            tableaux.append(right_child)
            tableaux.append(right_grandchild)

    def NECESSARY(node,open_children,world):
        formula = node.formula[1]
        for child in open_children:
            new_child = Node(formula=formula,parent=child,world=world,children=[])
            child.children.append(new_child)
            tableaux.append(new_child)

    def POSSIBLE(node,open_children,world):
        # from the bottom most node, create a new world branch, increment world counter
        # apply the rule
        world_formula = [f'{world-1}R{world}']
        formula = node.formula[1]
        for child in open_children:
            new_world_child = Node(formula=world_formula,parent=child,world=world,opensWorld=True,children=[])
            child.children.append(new_world_child)
            new_child = Node(formula=formula,parent=new_world_child,world=world,children=[])
            new_world_child.children.append(new_child)
            tableaux.append(new_world_child)
            tableaux.append(new_child)

    def NOTPOSSIBLE(node,open_children,world):
        formula = ['NEC',['NOT',node.formula[1][1]]]
        for child in open_children:
            new_child = Node(formula=formula,parent=child,world=world,children=[])
            child.children.append(new_child)
            tableaux.append(new_child)

    def NOTNECESSARY(node,open_children,world):
        formula = ['POS',['NOT',node.formula[1][1]]]
        for child in open_children:
            new_child = Node(formula=formula,parent=child,world=world,children=[])
            child.children.append(new_child)
            tableaux.append(new_child)

    # store the above in a map for easy access
    function_map = {
        'NOTNOT':NOTNOT,
        'IF':IF,
        'IFF':IFF,
        'XOR':XOR,
        'AND':AND,
        'OR':OR,
        'NOTAND':NOTAND,
        'NOTOR':NOTOR,
        'NOTIF':NOTIF,
        'NOTIFF':NOTIFF,
        'NECESSARY':NECESSARY,
        'POSSIBLE':POSSIBLE,
        'NOTPOSSIBLE':NOTPOSSIBLE,
        'NOTNECESSARY':NOTNECESSARY
    }

    # helper function to check if a given node matches one of the valid expansions
    def can_be_applied(node):
        if node.formula[0] == 'AND':
            return True, 'AND'
        elif node.formula[0] == 'IF':
            return True, 'IF'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'NOT':
            return True, 'NOTNOT'
        elif node.formula[0] == 'XOR':
            return True, 'XOR'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'IF':
            return True, 'NOTIF'
        elif node.formula[0] == 'OR':
            return True, 'OR'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'OR':
            return True, 'NOTOR'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'AND':
            return True, 'NOTAND'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'IFF':
            return True, 'NOTIFF'
        elif node.formula[0] == 'IFF':
            return True, 'IFF'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'NEC':
            return True, 'NOTNECESSARY'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'POS':
            return True, 'NOTPOSSIBLE'
        elif node.formula[0] == 'NEC':
            return True, 'NECESSARY'
        elif node.formula[0] == 'POS':
            return True, 'POSSIBLE'
        else:
            return False,None
    
    # helper function to check if one node is the negation of another (a contradiction)
    # contraction cannot occurr when nodes are in different worlds
    def contradiction(child_node, current_node):
        if child_node.world != current_node.world:
            return False
        elif type(current_node.formula) == str and child_node.formula == ['NOT', current_node.formula]:
            return True
        elif type(child_node.formula) == str and current_node.formula == ['NOT', child_node.formula]:
            return True
        elif type(current_node.formula) == list and child_node.formula == ['NOT', current_node.formula]:
            return True
        elif type(child_node.formula) == list and current_node.formula == ['NOT', child_node.formula]:
            return True
        else:
            return False


    root_node = Node(formula=F_expressions[0],parent=None,children=[],world=0)
    tableaux.append(root_node)
    parent = root_node

    # there are now an arbitrary number of formulae to start with
    # Initialize nodes for all of them and add them one after another
    for n in range(1,len(F_expressions)):
        node = Node(formula=F_expressions[n],parent=parent,children=[],world=0)
        tableaux.append(node)
        parent.children.append(node)
        parent = node
    

    # while some formulas have not been applied
    while True:
        # if we compleate a full pass through the tree without expanding anything
        # it means all rules have been applied
        # this keeps track of whether this is true
        all_branches_expaneded = True
        for index in range(len(tableaux)):
            open_children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
            if len(open_children) == 0:
                all_branches_expaneded = True
                break
            # check if the formula hasn't been applied (and if it can be)
            if tableaux[index].isApplied == False:
                if tableaux[index].opensWorld == True:
                    # skip over special nodes that create new worlds
                    continue
                is_appliable,rule = can_be_applied(tableaux[index])
                if is_appliable:

                    # increment the world counter, that way it is not used in the branch
                    if rule == 'POSSIBLE':
                        total_worlds += 1
                        all_branches_expaneded = False
                        POSSIBLE(tableaux[index],open_children,total_worlds)
                        tableaux[index].isApplied = True
                        all_branches_expaneded = False
                        break

                    elif rule == 'NECESSARY':
                        # do a backward walk up the tree, looking for branches that open new worlds under the current one
                        # if you find one, make a note of the world id and apply necessary operator
                        # otherwise, it can't be applied
                        child_ptr = open_children[0]
                        current_ptr = child_ptr
                        objs_in_branch = []
                        while True:
                            # do a backward walk up the tree
                            # keep track of how many child branches are open
                            # close branches with contradictions
                            current_ptr = current_ptr.parent
                            # check for terminating condition
                            if current_ptr == None:
                                break
                            
                            # check if it is a world creating node
                            # this causes an infinite loop if there is no possible operator to create a world
                            # but it will be caught by the timeout
                            if current_ptr.opensWorld == True:
                                NECESSARY(tableaux[index],open_children,world=current_ptr.world)
                                tableaux[index].isApplied = True
                                all_branches_expaneded = False
                                break
                        

                    else:
                        # get the rule we need to apply and call the function
                        # get the open children to expand on
                        if index == 0:
                            function_map[rule](tableaux[index],open_children,world=0)
                        else:
                            # the parent should always be in the same world
                            # except for nodes that open a new world, but they are always closed
                            function_map[rule](tableaux[index],open_children,world=tableaux[index].world)
                        # close the branch
                        tableaux[index].isApplied = True
                        all_branches_expaneded = False
                        break

        # check for open branches
        children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
        open_children = 0
        for child in children:
            child_ptr = child
            current_ptr = child_ptr
            while True:
                # do a backward walk up the tree
                # keep track of how many child branches are open
                # close branches with contradictions
                current_ptr = current_ptr.parent
                # check for terminating condition
                if current_ptr == None:
                    break
                if contradiction(child_ptr,current_ptr):
                    child_ptr.isApplied = True
                    break
            
            if child.isApplied == False:
                open_children += 1
        if len(children) == 0 or all_branches_expaneded:
            total_children = [node for node in tableaux if len(node.children) == 0]
            if open_children == len(total_children):
                return 'S'
            elif open_children == 0:
                return 'U'
            else:
                return 'S'

        # ensure we don't run out of time
        cur_time = time.time()
        if cur_time - start_time >= 50:
            return 'S'



def parseExpression(F):
    # Remove white space characters (except whitespaces) from the expression string
    def cleanup_expression(expr):
        return re.sub(r'[\t\n\r ]+', ' ', expr)

    # Create tree from expression string, raise error if expression is malformed
    def create_expression_tree(expression):
        expression = expression.strip()


        # If expression consists of just one symbol, just return it
        # the symbol could be a predicate, function, or objcect
        if re.match('[a-zA-Z0-9]+$', expression) and expression not in ['AND','OR','NOT','XOR','IF','IFF','NEC','POS']:
            return expression

        # Retrieve predicates, objects, functions, and operators
        #   Then, match operator, which could actually be an operator, or could be a predicate or function
        #   Then, match the rest as operand expression
        #   Also, do not forget, that a correct expression starts and ends with brackets
        operator, operand_expression = \
            re.match(r'\(([A-Za-z0-9-=]+)(.*)\)$', expression).groups()
        


        # Convert operand expression to list to be traversed
        operand_expression, operands = list(operand_expression.strip())[::-1], []

        # Loop until operand expression is fully processed
        while operand_expression:

            # Process first character
            operands.append(operand_expression.pop())

            # Check if current operand is a symbol or an expression
            # Use different stopping criteria for each of them
            if re.match('[a-z0-9]', operands[-1].strip()):
                while operand_expression and re.match('[a-z0-9]', operand_expression[-1]):
                    operands[-1] += operand_expression.pop()
            else:
                while operands[-1].count('(') != operands[-1].count(')'):
                    operands[-1] += operand_expression.pop()

            if operand_expression and not operand_expression[-1].strip():
                operand_expression.pop()

        # Handle unary operators
        if operator in ['NOT', 'NEC', 'POS']:
            return [operator, create_expression_tree(operands[0])]

        # Handle binary operators
        # Since quantifiers have similar structure to binary operators, also parse them here
        elif operator in ['IF', 'IFF', 'XOR']:
            return [
                operator,
                create_expression_tree(operands[0]),
                create_expression_tree(operands[1])
            ]

        # Handle operators which can be binary or more
        elif operator in ['AND', 'OR']:
            operands, result_expr = operands[::-1], []
            current_expr = result_expr

            # If there are more than two operands, they need to be converted to a tree so that
            # only two operands are present at each level
            while operands:

                # Handle more than two operands
                # One is recursively converted to an expression and added as the first operand
                # An expression is places instead of the second operand, and currently processed
                # expression is re-assigned to newly created empty expression
                # That way, the remaining operands are going to be added to that sub-expression,
                # forming a tree.
                current_expr.extend([operator])
                while operands:
                    current_expr.extend([create_expression_tree(operands.pop())])


            return result_expr

        else:
            # if it's not an operator, it must be either a predicate or a function
            # either way, we process it the same
            operands, result_expr = operands[::-1], []
            current_expr = result_expr
            if len(operands) == 0:
                current_expr += [operator]
            elif len(operands) == 1:
                current_expr += [operator, create_expression_tree(operands[0])]
            else:
                # in this case, there will always be at least 2 child remaining
                # basically we parse the tree in the same way as we did for the project
                current_expr.extend([operator])
                while operands:
                    current_expr.extend([create_expression_tree(operands.pop())])

            return result_expr
        


    # Clean up the expression string
    F = cleanup_expression(F)

    # Construct expression tree, assume that expression is valid for this assignment.
    # Also find predicates, functions, and objects in the tree
    # need to read these in as we create the tree
    expr = create_expression_tree(F)

    return expr