"""
    CAP 6632 Homework 4
    Antonio Laverghetta Jr.
"""

import re
import time
import string
import random
from copy import copy, deepcopy


# Given an S-expression, return whether the formulae is satisfiable
def isSatisfiable(F):
    # Build syntax tree, one for each formula
    F_expressions = []
    start_time = time.time()
    # keep track of all quantified variables and objects
    quantified_variables = set()
    objects = []
    for f in F:
        f_exp, q, o  = parseExpression(f)
        F_expressions.append(f_exp)
        quantified_variables = quantified_variables.union(q)
        [objects.append(obj) for obj in o if obj not in objects]

    # run Tableaux to prove sat or unsat
    return tableaux(F_expressions, quantified_variables, objects, start_time)


def tableaux(F_expressions, quantified_variables, objects, start_time):
    # in the tableaux, each formula is a node in a tree
    # a node contains the formula
    # a flag to indicate whether the formula has been applied
    # a pointer to the parent
    # a list of pointers to the children (in order of traversal)
    # the root node (the formula we are passed) has a parent pointer of null
    # likewise, the children are null initially and are added as we build the tree

    class Node():
        def __init__(self, formula, parent, children):
            self.formula = formula
            self.parent = parent
            self.children = children
            self.isApplied = False  # True means the node is closed
            # only for universal instantiation, keep track of all nodes that have been introduced 
            self.introducedObjects = []
    
    # the tableaux is simply a list of nodes for easy traversal
    tableaux = []

    # helper function, create a new random object
    def gen_object():
        letters = string.ascii_lowercase
        numbers = string.digits
        while True:
            new_obj = ''.join(random.choice(letters) + random.choice(numbers) for i in range(32))
            if new_obj not in objects:
                return new_obj
    
    # helper function, find all objects in the formula
    # via a recursive search
    def get_objects(F_tree, parent, objects):
        # skip over operators
        if F_tree[0] not in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
            # if the parent is an operator
            if parent in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
                if type(F_tree) == str:
                    return objects
                else:
                    # add all children as objects
                    # for i in range(1,len(F_tree)):
                    #     objects.append(F_tree[i])
                    [objects.append(F_tree[o]) for o in range(1,len(F_tree)) if F_tree[o] not in objects]
                    return objects
            # if the parent is a predicate and there are children
            # elif type(F_tree) == list  and len(F_tree) != 1:
            #     objects.append(F_tree)
            #     return objects
            # # or the function could have zero children
            # elif parent in predicates and type(F_tree) == list and len(F_tree) == 1:
            #     objects.append(F_tree)
            #     return objects

        # handle the children recursively
        if len(F_tree) == 1 or type(F_tree) == str:
            # base case, return if no more leaves to explore
            return objects
        elif len(F_tree) == 2:
            # 1 child
            parent = F_tree[0]
            objects = get_objects(F_tree[1],parent,objects)
            return objects
        else:
            # 2 or more children
            parent = F_tree[0]
            # handle quantifiers, the first child is NOT an object
            if parent in ['EXISTS','FORALL']:
                objects = get_objects(F_tree[2],parent,objects)
                return objects
            else:
                for child in range(1,len(F_tree)):
                    objects = get_objects(F_tree[child],parent,objects)
                return objects
    
    # helper function for instantiation
    # given a wff and a quantified variable q, replace every q with constant c
    def replace_quantified_variables(F_tree,parent,q,c):
        if F_tree[0] not in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
            # if the parent is an operator
            if parent in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
                if type(F_tree) == str:
                    # a lone predicate, just return
                    return
                else:
                    # find and replace the quantified variable
                    for o in range(1,len(F_tree)):
                        if F_tree[o] == q:
                            F_tree[o] = c
                    return F_tree
            # # if the parent is a predicate and there are children
            # elif type(F_tree) == list and parent in predicates and len(F_tree) != 1:
            #     objects.append(F_tree)
            #     return
            # # or the function could have zero children
            # elif parent in predicates and type(F_tree) == list and len(F_tree) == 1:
            #     objects.append(F_tree)
            #     return

        # otherwise, recurisvely search
        if len(F_tree) == 1 or type(F_tree) == str:
            # base case, return if no more leaves to explore
            return F_tree
        elif len(F_tree) == 2:
            # 1 child
            parent = F_tree[0]
            F_tree[1] = replace_quantified_variables(F_tree[1],parent,q,c)
            return F_tree
        else:
            # 2 or more children
            parent = F_tree[0]
            # handle quantifiers, the first child is NOT an object
            if parent in ['EXISTS','FORALL']:
                F_tree[2] = replace_quantified_variables(F_tree[2],parent,q,c)
                return F_tree
            else:
                for child in range(1,len(F_tree)):
                    F_tree[child] = replace_quantified_variables(F_tree[child],parent,q,c)
                return F_tree

    # define functions to handle each expansion
    # given the node to expand and the children
    def NOTEXISTS(node, open_children):
        # change existential to universal
        # push negation inward
        # mark the node as closed and return
        arg = copy(node.formula[1])
        arg[0] = 'FORALL'
        arg[2] = ['NOT',arg[2]]
        for child in open_children:
            new_child = Node(formula=arg,parent=child,children=[])
            tableaux.append(new_child)
            child.children.append(new_child)

    def NOTFORALL(node, open_children):
        # change universal to existential
        # push negation inward
        # mark the node as closed and return
        arg = copy(node.formula[1])
        arg[0] = 'EXISTS'
        arg[2] = ['NOT',arg[2]]
        for child in open_children:
            new_child = Node(formula=arg,parent=child,children=[])
            tableaux.append(new_child)
            child.children.append(new_child)

    def UNIVERSALINSTANTIATION(node,objects,open_children):
        # for all objects in the tableaux that have not yet been instantiated using this node:
        #   apply instantion to the object
        new_objects = [o for o in objects if o not in node.introducedObjects]
        # get rid of quantified variables (cant do this in comprehension because lists aren't hashable)
        while True:
            complete = True
            for o in new_objects:
                if type(o) == str and o in quantified_variables:
                    complete = False
                    new_objects.remove(o)
            if complete:
                break
                
        
        if len(new_objects) == 0:
            # if there are no objects that are not quantified variables, create a new object and use that for the rule
            new_obj = gen_object()
            arg = deepcopy(node.formula[2])
            # replace the quantified varaible with the new object
            arg = replace_quantified_variables(arg,'FORALL',node.formula[1],new_obj)
            # add newly created objects (if any) to the set of objects in the tableaux
            objects.append(new_obj)
            node.introducedObjects.append(new_obj)
            for child in open_children:
                new_child = Node(formula=arg,parent=child,children=[])
                tableaux.append(new_child)
                child.children.append(new_child)
            
            return
        else:
            # apply the rule for all the objects simulatenously
            for obj in new_objects:
                arg = deepcopy(node.formula[2])
                arg = replace_quantified_variables(arg,'FORALL',node.formula[1],obj)
                open_children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
                node.introducedObjects.append(obj)
                for child in open_children:
                    new_child = Node(formula=arg,parent=child,children=[])
                    tableaux.append(new_child)
                    child.children.append(new_child)
            # do NOT close the node and return
            return

        
        
    def EXISTENTALINSTANTIATION(node,object,open_children):
        # apply instantiation to the object
        # close the node and return
        if object == None:
            new_obj = gen_object()
            arg = copy(node.formula[2])
            # replace the quantified varaible with the new object
            arg = replace_quantified_variables(arg,'EXISTS',node.formula[1],new_obj)
            # add newly created objects (if any) to the set of objects in the tableaux
            objects.append(new_obj)
            for child in open_children:
                new_child = Node(formula=arg,parent=child,children=[])
                tableaux.append(new_child)
                child.children.append(new_child)
            
            return
        else:
            # apply the rule for all the objects simulatenously
            arg = copy(node.formula[2])
            arg = replace_quantified_variables(arg,'EXISTS',node.formula[1],object)
            for child in open_children:
                new_child = Node(formula=arg,parent=child,children=[])
                tableaux.append(new_child)
                child.children.append(new_child)
            return

    def NOTNOT(node,open_children):
        # strip out double negative
        arg = node.formula[1][1]
        for child in open_children:
            new_child = Node(formula=arg,parent=child,children=[])
            tableaux.append(new_child)
            child.children.append(new_child)
    
    def IF(node,open_children):
        # create the children
        left_arg = ['NOT',node.formula[1]]

        right_arg = node.formula[2]
        # append to every open branch
        for child in open_children:
            left_child = Node(formula=left_arg,parent=child,children=[])
            right_child = Node(formula=right_arg,parent=child,children=[])
            tableaux.append(left_child)
            tableaux.append(right_child)
            child.children.append(left_child)
            child.children.append(right_child)


    def IFF(node,open_children):
        # create the children
        left_normal = node.formula[1]
        left_negated = ['NOT', node.formula[1]]
        right_normal = node.formula[2]
        right_negated = ['NOT',node.formula[2]]

        for child in open_children:
            # first the left branch
            left_child = Node(formula=left_normal,parent=child,children=[])
            child.children.append(left_child)
            left_grandchild = Node(formula=right_normal,parent=left_child,children=[])
            left_child.children.append(left_grandchild)

            # then the right
            right_child = Node(formula=left_negated,parent=child,children=[])
            child.children.append(right_child)
            right_grandchild = Node(formula=right_negated,parent=right_child,children=[])
            right_child.children.append(right_grandchild)

            # add all nodes inorder
            tableaux.append(left_child)
            tableaux.append(left_grandchild)
            tableaux.append(right_child)
            tableaux.append(right_grandchild)

    def XOR(node,open_children):
        # create the children
        left_normal = node.formula[1]
        left_negated = ['NOT', node.formula[1]]
        right_normal = node.formula[2]
        right_negated = ['NOT',node.formula[2]]

        for child in open_children:
            # first the left branch
            left_child = Node(formula=left_negated,parent=child,children=[])
            child.children.append(left_child)
            left_grandchild = Node(formula=right_normal,parent=left_child,children=[])
            left_child.children.append(left_grandchild)

            # then the right
            right_child = Node(formula=left_normal,parent=child,children=[])
            child.children.append(right_child)
            right_grandchild = Node(formula=right_negated,parent=right_child,children=[])
            right_child.children.append(right_grandchild)

            # add all nodes inorder
            tableaux.append(left_child)
            tableaux.append(left_grandchild)
            tableaux.append(right_child)
            tableaux.append(right_grandchild)

    def AND(node,open_children):
        # get the args of and
        args = node.formula[1:]
        for child in open_children:
            parent = child
            for arg in args:
                # create a new node and append it to the tableaux
                new_node = Node(formula=arg,parent=parent,children=[])
                tableaux.append(new_node)
                parent.children.append(new_node)
                parent = new_node

    def OR(node,open_children):
        args = node.formula[1:]
        for child in open_children:
            for arg in args:
                new_node = Node(formula=arg,parent=child,children=[])
                child.children.append(new_node)
                tableaux.append(new_node)

    def NOTAND(node,open_children):
        args = node.formula[1][1:]
        # negate the args
        args = [['NOT',arg] for arg in args]

        for child in open_children:
            for arg in args:
                new_node = Node(formula=arg,parent=child,children=[])
                child.children.append(new_node)
                tableaux.append(new_node)

    def NOTOR(node,open_children):
        # get the args of and
        args = node.formula[1][1:]
        # negate the args
        args = [['NOT',arg] for arg in args]

        for child in open_children:
            parent = child
            for arg in args:
                # create a new node and append it to the tableaux
                new_node = Node(formula=arg,parent=parent,children=[])
                tableaux.append(new_node)
                parent.children.append(new_node)
                parent = new_node

    def NOTIF(node,open_children):
        left_child = node.formula[1][1]
        right_child = ['NOT', node.formula[1][2]]
        
        for child in open_children:
            new_node = Node(formula=left_child,parent=child,children=[])
            child.children.append(new_node)
            new_node_child = Node(formula=right_child,parent=new_node,children=[])
            new_node.children.append(new_node_child)

            tableaux.append(new_node)
            tableaux.append(new_node_child)

    def NOTIFF(node,open_children):
        # create the children
        left_normal = node.formula[1][1]
        left_negated = ['NOT', node.formula[1][1]]
        right_normal = node.formula[1][2]
        right_negated = ['NOT',node.formula[1][2]]

        for child in open_children:
            # first the left branch
            left_child = Node(formula=left_normal,parent=child,children=[])
            child.children.append(left_child)
            left_grandchild = Node(formula=right_negated,parent=left_child,children=[])
            left_child.children.append(left_grandchild)

            # then the right
            right_child = Node(formula=left_negated,parent=child,children=[])
            child.children.append(right_child)
            right_grandchild = Node(formula=right_normal,parent=right_child,children=[])
            right_child.children.append(right_grandchild)

            # add all nodes inorder
            tableaux.append(left_child)
            tableaux.append(left_grandchild)
            tableaux.append(right_child)
            tableaux.append(right_grandchild)

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
        'NOTEXISTS':NOTEXISTS,
        'NOTFORALL':NOTFORALL,
        'UNIVERSALINSTANTIATION':UNIVERSALINSTANTIATION,
        'EXISTENTALINSTANTIATION':EXISTENTALINSTANTIATION
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
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'EXISTS':
            return True, 'NOTEXISTS'
        elif node.formula[0] == 'NOT' and node.formula[1][0] == 'FORALL':
            return True, 'NOTFORALL'
        elif node.formula[0] == 'FORALL':
            return True, 'UNIVERSALINSTANTIATION'
        elif node.formula[0] == 'EXISTS':
            return True, 'EXISTENTALINSTANTIATION'
        else:
            return False,None
    
    # helper function to check if one node is the negation of another (a contradiction)
    def contradiction(child_node, current_node):
        if type(current_node.formula) == str and child_node.formula == ['NOT', current_node.formula]:
            return True
        elif type(child_node.formula) == str and current_node.formula == ['NOT', child_node.formula]:
            return True
        elif type(current_node.formula) == list and child_node.formula == ['NOT', current_node.formula]:
            return True
        elif type(child_node.formula) == list and current_node.formula == ['NOT', child_node.formula]:
            return True
        else:
            return False

    # helper function for checking equivalence
    # given 2 predicates, check that it's possible to make equivalence substitutions on them
    # however, it should also work with functions or even objects
    # assumes that you have already found all equivalence relations
    def check_predicate_equivalence(pred_1,pred_2,equivalent_objs):
        # the total number of functions and objects must match for replacements to be possible
        if len(pred_1) == len(pred_2):
            for i in range(len(pred_1)):
                # at each position they must both be the same type, otherwise the signatures are different
                if type(pred_1[i]) != type(pred_2[i]):
                    return False
                elif type(pred_1[i]) == list:
                    # recursively check each expression
                    check_predicate_equivalence(pred_1[i],pred_2[i],equivalent_objs)
                elif type(pred_1[i]) == str:
                    # they could either be functions or objects
                    # if they're functions they must match
                    # if they're objects they must be covered by the same equivalence relation
                    if pred_1[i] == pred_2[i]:
                        continue
                    else:
                        covered = False
                        for e in equivalent_objs:
                            if pred_1[i] in e and pred_2[i] in e:
                                covered = True
                                break
                        if covered:
                            continue
                        else:
                            return False
            
            return True
        else:
            return False
    
    # helper function to deal with applying identitiy rules (if applicable)
    # HW4: the node that leads to a contradiction could be anywhere in the branch,
    # so we need to check all of them and cross the child node off
    def make_object_substitutions(children):
        for child in children:
            equivalent_objs = []
            child_ptr = child
            child_exp = child.formula
            current_ptr = child_ptr
            # on the first walk, find equalities for THIS branch, ignoring the others
            while True:
                current_ptr = current_ptr.parent
                # check for terminating condition
                if current_ptr == None:
                    break
                
                if current_ptr.formula[0] != '=':
                    continue
                else:
                    if current_ptr.formula[1:] not in equivalent_objs:
                        equivalent_objs.append(current_ptr.formula[1:]) 

            # On the second walk, using the found equalities, check and elimiate contradictions
            # If none were found, just return
            if equivalent_objs == []:
                return False
            current_ptr = child_ptr
            while True:
                # do a backward walk up the tree
                # keep track of how many child branches are open
                # close branches with contradictions
                current_ptr = current_ptr.parent
                # check for terminating condition
                if current_ptr == None:
                    return False
                # 1st case: child is negated
                if child_exp[0] == 'NOT':
                    # the second part checks whether the objects are the same
                    if current_ptr.formula[0] == child_exp[1][0]:
                        is_equivalent = check_predicate_equivalence(current_ptr.formula[1:],child_exp[1][1:],equivalent_objs)
                        if is_equivalent:
                            # if we get here, then we know there must be a contradiction
                            # it isn't actually necessary to find the specific object to predicate assignment
                            # we can stop the traversal after crossing off the branch
                            child.isApplied = True
                            return True

                # 2nd case: child isn't negated
                elif current_ptr.formula[0] == 'NOT':
                    if current_ptr.formula[1][0] == child_exp[0]:
                        is_equivalent = check_predicate_equivalence(current_ptr.formula[1][1:],child_exp[1:],equivalent_objs)
                        if is_equivalent:
                            child.isApplied = True
                            return True
                else:
                    continue
    
    # helper function hanlde symmetry
    # these are cases where all rules have been applied and subsitiution have been made
    # however, there are still contradictions which can only be derived using identity
    # 1. The negation of an object and itself always leads to contradiction, this is true if
    #   a. If there are 1 or more nested function calls which match
    #   b. The functions take multiple args that are all the same object
    #   c. It is simply the negation of two of the same object
    # 2. The negation of an object and a subsitutiable object always leads to contradiction
    #   a. All of the rules mentioned for 1 also apply here
    def check_for_symmetry(children):
        # in the first pass, see if the child itself is a contradiction
        for child in children:
            # the simpliest case is the negation of the same object
            if child.formula[0] == 'NOT' and child.formula[1][0] == '=' and check_predicate_equivalence(child.formula[1][1],child.formula[1][2],[]):
                child.isApplied = True
                continue
            equivalent_objs = []
            child_ptr = child
            child_exp = child.formula
            current_ptr = child_ptr
            # on the first walk, find equalities for THIS branch, ignoring the others
            while True:
                current_ptr = current_ptr.parent
                # check for terminating condition
                if current_ptr == None:
                    break
                
                if current_ptr.formula[0] != '=':
                    continue
                else:
                    equivalent_objs.append(current_ptr.formula[1:])
            

            # for symmetry cases the child should always be negated (otherwise we cant derive a contradiction)
            # there may be nested function calls, so we have to ensure:
            #   1. The function calls match
            #   2. The objects are covered by an equivalence relation
            if child_exp[0] == 'NOT' and child_exp[1][0] == '=':
                if check_predicate_equivalence(child_exp[1][1],child_exp[1][2],equivalent_objs):
                    # if we get here, then we know there must be a contradiction
                    # it isn't actually necessary to find the specific object to predicate assignment
                    # we can stop the traversal after crossing off the branch
                    child.isApplied = True
                    return

            else:
                continue
        # in the second pass, look for contradictions farther up the tree
        # if so, close this branch
        for child in children:
            # the simpliest case is the negation of the same object 
            child_ptr = child
            child_exp = child.formula
            current_ptr = child_ptr
            # on the first walk, find equalities for THIS branch, ignoring the others
            while True:
                current_ptr = current_ptr.parent
                # check for terminating condition
                if current_ptr == None:
                    break
                if current_ptr.formula[0] == 'NOT' and current_ptr.formula[1][0] == '=':
                    child.isApplied = True
                    break



    root_node = Node(formula=F_expressions[0],parent=None,children=[])
    tableaux.append(root_node)
    parent = root_node

    # there are now an arbitrary number of formulae to start with
    # Initialize nodes for all of them and add them one after another
    for n in range(1,len(F_expressions)):
        node = Node(formula=F_expressions[n],parent=parent,children=[])
        tableaux.append(node)
        parent.children.append(node)
        parent = node
    

    # while some formulas have not been applied
    while True:
        # if we compleate a full pass through the tree without expanding anything
        # it means all rules have been applied
        # this keeps track of whether this is true
        all_branches_expaneded = True
        appliable_rules = []
        for index in range(len(tableaux)):
            # check if the formula hasn't been applied (and if it can be)
            if tableaux[index].isApplied == False:
                is_appliable,rule = can_be_applied(tableaux[index])
                if is_appliable:
                    open_children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
                    # universal rules can be applied infinitely many times
                    # this ensures we stop if all the brances are closed
                    if len(open_children) == 0:
                        all_branches_expaneded = True
                        break
                    # hold off on universal instantiaion until all other rules have been applied
                    if rule == 'UNIVERSALINSTANTIATION':
                        appliable_rules.append(tableaux[index])
                        all_branches_expaneded = False
                        continue

                    elif rule == 'EXISTENTALINSTANTIATION':
                        # do a backward walk up the tree, keep track of the objects at each node
                        # call existential elimination using only the nodes not present in the current path (or none if there are no such nodes)
                        appliable_rules = []
                        child_ptr = tableaux[index]
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
                            # get the objects from this node
                            current_objs = get_objects(current_ptr.formula,parent=None,objects=[])
                            [objs_in_branch.append(obj) for obj in current_objs if obj not in objs_in_branch]
                        
                        new_objs = [o for o in objects if o not in objs_in_branch and o]
                        # get rid of quantified variables (cant do this in comprehension because lists aren't hashable)
                        while True:
                            complete = True
                            for o in new_objs:
                                if type(o) == str and o in quantified_variables:
                                    complete = False
                                    new_objs.remove(o)
                            if complete:
                                break
                        if len(new_objs) != 0:
                            EXISTENTALINSTANTIATION(tableaux[index],new_objs[0],open_children)
                        else:
                            EXISTENTALINSTANTIATION(tableaux[index],None,open_children)
                        tableaux[index].isApplied = True
                        all_branches_expaneded = False

                    else:
                        # get the rule we need to apply and call the function
                        # get the open children to expand on
                        appliable_rules = []
                        function_map[rule](tableaux[index],open_children)
                        # close the branch
                        tableaux[index].isApplied = True
                        all_branches_expaneded = False
                        break
        
        # assuming we get through the above with entries in this list, it means we can only apply universal instantiation
        # so, go through them all at once
        # however, prefer to go through rules which haven't been applied at all yet (if any)
        # since these will possibly avoid creating new objects
        open_children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
        new_rules = []
        for rule in appliable_rules:
            if rule.introducedObjects == []:
                new_rules.append(rule)
        if len(new_rules) != 0:
            for rule in new_rules:
                UNIVERSALINSTANTIATION(rule,objects,open_children)
        # if not, go through all of them, which is likely to lead to new objects
        else:
            for rule in appliable_rules:
                UNIVERSALINSTANTIATION(rule,objects,open_children)
        
        
        
        # find all child branches, ignoring branches that have already been closed
        children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
        # check for object subsition
        # and also for applications of identity (first updating child list so we don't iterate through closed branches)
        # if all_branches_expaneded and len(children) != 0:
        for child in children:
            parent_nodes = []
            child_ptr = child
            child_exp = child.formula
            current_ptr = child_ptr
            # on the first walk, find equalities for THIS branch, ignoring the others
            while True:
                current_ptr = current_ptr.parent
                # check for terminating condition
                if current_ptr == None:
                    break
                parent_nodes.append(current_ptr)
            
            is_applied_parents = make_object_substitutions(parent_nodes)
            # but don't forget to also check the child node
            is_applied_child = make_object_substitutions([child])
            if is_applied_parents or is_applied_child:
                child.isApplied = True
                continue
        # for symmetry, the contradiction could be any node in the tree,
        # so, look for all nodes that havent been crossed out yet from the child node
        # if there is one, close the child
        children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
        check_for_symmetry(children)
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

        # check for open branches
        children = [node for node in tableaux if node.isApplied == False and len(node.children) == 0]
        if len(children) == 0 or all_branches_expaneded:
            total_children = [node for node in tableaux if len(node.children) == 0]
            if open_children == len(total_children):
                return 'S'
            elif open_children == 0:
                return 'U'
            else:
                return 'S'

        # prevent infinite recursion (to be safe set to 10 seconds less than the max)
        cur_time = time.time()
        if cur_time - start_time >= 95:
            return 'S'



def parseExpression(F):
    objects = []
    quantified_variables = set()
    predicates = set()

    # after building the syntax tree, recusrively find all
    # predicates, objects, and functions
    # on every level

    # For HW4: Changed this slightly
    # we no longer need to track each separately but functions and objects need to be tracked for universal instantiation
    def find_pfo(F_tree, predicates, parent):
        # determine what the current term is
        if parent == None and F_tree[0] not in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
            # base case where there is a predicate at the top level
            predicates.add(F_tree[0])
        else:
            # skip over operators
            if F_tree[0] not in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
                # if the parent is an operator
                if parent in ['AND','OR','NOT','XOR','IF','IFF', 'FORALL', 'EXISTS']:
                    if type(F_tree) == str:
                        predicates.add(F_tree)
                    else:
                        predicates.add(F_tree[0])
                        # add all children as objects
                        # for i in range(1,len(F_tree)):
                        #     objects.append(F_tree[i])
                        [objects.append(F_tree[o]) for o in range(1,len(F_tree)) if F_tree[o] not in objects]
                        return
                # if the parent is a predicate and there are children
                elif type(F_tree) == list and parent in predicates and len(F_tree) != 1:
                    objects.append(F_tree)
                    return
                # or the function could have zero children
                elif parent in predicates and type(F_tree) == list and len(F_tree) == 1:
                    objects.append(F_tree)
                    return
                elif parent in predicates and type(F_tree) == str:
                    objects.append(F_tree)
                    return

        # handle the children recursively
        if len(F_tree) == 1 or type(F_tree) == str:
            # base case, return if no more leaves to explore
            return
        elif len(F_tree) == 2:
            # 1 child
            parent = F_tree[0]
            find_pfo(F_tree[1],predicates,parent)
            return
        else:
            # 2 or more children
            parent = F_tree[0]
            # handle quantifiers, the first child is NOT an object
            if parent in ['EXISTS','FORALL']:
                find_pfo(F_tree[2],predicates,parent)
                return
            else:
                for child in range(1,len(F_tree)):
                    find_pfo(F_tree[child],predicates,parent)
                return
    
    # Remove white space characters (except whitespaces) from the expression string
    def cleanup_expression(expr):
        return re.sub(r'[\t\n\r ]+', ' ', expr)

    # Create tree from expression string, raise error if expression is malformed
    def create_expression_tree(expression):
        expression = expression.strip()


        # If expression consists of just one symbol, just return it
        # the symbol could be a predicate, function, or objcect
        if re.match('[a-zA-Z0-9]+$', expression) and expression not in ['AND','OR','NOT','XOR','IF','IFF','=','EXISTS','FORALL']:
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
        if operator == 'NOT':
            return [operator, create_expression_tree(operands[0])]

        # Handle binary operators
        # Since quantifiers have similar structure to binary operators, also parse them here
        elif operator in ['IF', 'IFF', 'XOR', '=']:
            return [
                operator,
                create_expression_tree(operands[0]),
                create_expression_tree(operands[1])
            ]
        
        elif operator in ['EXISTS', 'FORALL']:
            quantified_varaible = operands[0]            
            quantified_variables.add(quantified_varaible)
            return [
                operator,
                quantified_varaible,
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
    # to make things simplier, add = to the predicates
    # its removed before return from isSatisfiable

    # For HW4: Don't need to do this but leaving the function here just in case
    find_pfo(expr,predicates,parent=None)


    return expr, quantified_variables, objects