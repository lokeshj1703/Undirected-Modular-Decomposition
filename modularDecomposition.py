# -*- coding: utf-8 -*-
r"""
Modular Decomposition

This module implements the function for computing the modular decomposition
of undirected graphs.


#*****************************************************************************
#       Copyright (C) 2013 YOUR NAME <your email>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************
"""

from sage.all import Graph

PRIME = 0
SERIES = 1
PARALLEL = 2
NORMAL = 3
FOREST = -1
LEFT_SPLIT = 1
RIGHT_SPLIT = 2
BOTH_SPLIT = 3
NO_SPLIT = 0
LEFT_OF_SOURCE = -1
RIGHT_OF_SOURCE = 1
SOURCE = 0

class Queue:

    def __init__(self):
        self.q = []

    def put(self, ele):
        self.q.append(ele)

    def empty(self):
        if not self.q:
            return True
        return False

    def get(self):
        if self.empty():
            return ValueError("Queue is empty")
        return self.q.pop(0)

    def clear(self):
        self.q = []

class NodeInfo:
    """Node class stores information about the node type,
       node split and index of the node in the parent tree.
       Node type can be PRIME, SERIES, PARALLEL, NORMAL or FOREST.
       Node split can be NO_SPLIT, LEFT_SPLIT, RIGHT_SPLIT or BOTH_SPLIT.
       A node is split in the refinement phase and the split used is propagated to
       the ancestors.

       - ``node_type`` -- Specifies the type of node

            * ``"PARALLEL"`` -- indicates the node is a parallel module

            * ``"SERIES"`` -- indicates the node is a series module

            * ``"PRIME"`` -- indicates the node is a prime module

            * ``"FOREST"`` -- indicates a forest containing trees

            * ``"NORMAL"`` -- indicates the node is normal containing a vertex

       - ``node_split`` -- Specifies the type of splits which have occurred in
                           the node and its descendants

            * ``"LEFT_SPLIT"`` -- indicates a left split has occurred

            * ``"RIGHT_SPLIT"`` -- indicates a right split has occurred

            * ``"BOTH_SPLIT"`` -- indicates both left and right split have occurred

            * ``"NO_SPLIT"`` -- indicates no split has occurred

       - ``index_in_root`` -- specifies the index of the node in the forest obtained
                              after promotion phase

       - ``comp_num`` -- specifies the number given to nodes in a (co)component
                         before refinement

       - ``is_separated`` -- specifies whether a split has occurred with the node as
                             the root

    """

    def __init__(self, node_type):
        self.node_type = node_type
        self.node_split = NO_SPLIT
        self.index_in_root = -1
        self.comp_num = -1
        self.is_separated = False

    def set_node_split(self, node_split):
        """
        Adds node_split to the node split of self. LEFT_SPLIT and
        RIGHT_SPLIT can exist together in self as BOTH_SPLIT.

        INPUT:

        - ``node_split`` -- node_split to be added to self

        """
        if self.node_split == NO_SPLIT:
            self.node_split = node_split
        elif ((self.node_split == LEFT_SPLIT and node_split == RIGHT_SPLIT) or
              (self.node_split == RIGHT_SPLIT and node_split == LEFT_SPLIT)):
            self.node_split = BOTH_SPLIT

    def has_left_split(self):
        """
        Returns true if self has LEFT_SPLIT

        """
        return self.node_split==LEFT_SPLIT or self.node_split==BOTH_SPLIT

    def has_right_split(self):
        """
        Returns true if self has RIGHT_SPLIT

        """
        return self.node_split==RIGHT_SPLIT or self.node_split==BOTH_SPLIT

    def __str__(self):
        string = ""
        if self.node_type==SERIES:
            string += "SERIES"
        elif self.node_type==PARALLEL:
            string += "PARALLEL"
        elif self.node_type==PRIME:
            string += "PRIME"
        elif self.node_type==FOREST:
            string += "FOREST"
        else:
            string += "NORMAL"

        return string

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        return self.node_type == other.node_type

def modular_decomposition(graph):
    """
    Computes modular decomposition tree for the input graph.
    The tree structure is represented in form of nested lists.
    A tree node is a list with two elements. The first element is
    object of class NodeInfo and second element is a list which
    contains other tree nodes.

    INPUT:

    - ``graph`` -- The graph for which modular decompostion
                  tree needs to be computed

    OUTPUT:

    A nested list representing the modular decomposition tree computed
    for the graph
    """
    if graph._directed:
        return ValueError("Graph must be undirected")
    if graph.order() == 0:
        return create_prime_node()
    if graph.order() == 1:         #Single vertex graph
        root = create_normal_node(next(graph.vertex_iterator()))
        return root

    if not graph.is_connected():
        #Parallel case:- The tree contains the MD trees
        # of its connected components as subtrees
        components = graph.connected_components()
        root = create_parallel_node()
        for component in components:
            root[1].append(modular_decomposition(graph.subgraph(component)))
        return root
    elif graph.complement().is_connected():
        root = create_prime_node()
    else:
        root = create_series_node()

    bfs_generator = graph.breadth_first_search(next(graph.vertex_iterator()),
                                               report_distance=True)
    prev_level_distance = -1    #used as a demarker for different levels in bfs
    prev_level_list = []    #stores the vertices in previous level
    vertex_dist = {}        #dictionary stores the distance of vertices from the SOURCE
    vertex_status = {}      #dictionary stores the position of vertices w.r.t SOURCE
    vertex_status[next(graph.vertex_iterator())] = SOURCE
    for (vertex, distance) in bfs_generator:
        vertex_dist[vertex] = distance
        #Different distances from the source vertex are considered
        # as different levels in the algorithm

        # Mark the neighbours of source as LEFT_OF_SOURCE
        # as they appear to left of source in the forest
        # other vertices are marked as RIGHT_OF_SOURCE
        if distance == 1:
            vertex_status[vertex] = LEFT_OF_SOURCE
        elif distance != 0:
            vertex_status[vertex] = RIGHT_OF_SOURCE
        if distance != prev_level_distance: #On start of new level in BFS
            if prev_level_list:
                #MD Tree is computed for each level and added to the forest
                root[1].append(modular_decomposition(graph.subgraph(prev_level_list)))
            prev_level_list = []
            prev_level_distance = distance
        prev_level_list.append(vertex)

    #The last level is left out in the above loop
    root[1].append(modular_decomposition(graph.subgraph(prev_level_list)))

    #The MD tree for the neighbours of source marked as LEFT_OF_SOURCE
    # are placed left of Source in the forest. root[1][1] is the source
    # and root[1][0] is the MD tree for the neighbours therefore the
    # the first two elements in the list are replaced
    temp = root[1][1]
    root[1][1] = root[1][0]
    root[1][0] = temp

    root[0].node_type = FOREST
    clear_node_split_info(root)
    number_cocomponents(root, vertex_status)
    number_components(root, vertex_status)
    refine(graph, root, vertex_dist, vertex_status)
    promote_left(root)
    promote_right(root)
    promote_child(root)
    assembly(graph, root, vertex_status, vertex_dist)

    if root[0].node_type==FOREST:
        return root[1][0]
    else:
        return root

def test_modular_decomposition(tree, graph):
    """
    This function tests the input modular decomposition tree using recursion.

    INPUT:

    - ``tree`` -- Modular decomposition tree to be tested
    - ``graph`` -- Graph whose modular decomposition tree needs to be tested

    OUTPUT:

    ``True`` if input ``tree`` is a modular decomposition else ``False``

    """
    if tree[0].node_type != NORMAL:
        for module in tree[1]:
            if not test_module(module, graph):
                #test whether modules pass the defining characteristics of modules
                return False
            if not test_modular_decomposition(module, graph.subgraph(get_vertices(module))):
                #recursively test the modular decompostion subtrees
                return False
        if not test_maximal_modules(tree, graph):
            # test whether the mdoules are maximal in nature
            return False
    return True

def test_maximal_modules(tree, graph):
    """
    This function tests maximal nature of modules in a modular decomposition tree. Suppose the
    module M = [M1, M2, ..., Mn] is the input modular decomposition tree. Algorithm forms pairs like
    (M1, M2), (M1, M3), ...(M1, Mn); (M2, M3), (M2, M4), ...(M2, Mn); ... and so on and tries to form
    a module using the pair. If the module formed has same type as M and is of type SERIES or
    PARALLEL then the formed module is not considered maximal. Otherwise it is considered maximal
    and M is not a modular decomposition tree.

    INPUT:

    - ``tree`` -- Modular decomposition tree whose modules are tested for maximal nature
    - ``graph`` -- Graph whose modular decomposition tree is tested

    OUTPUT:

    ``True`` if all modules at first level in the modular ddecomposition tree are
    maximal in nature

    """
    if tree[0].node_type!=NORMAL:
        for index, module in enumerate(tree[1]):
            for other_index in range(index+1, len(tree[1])):
                module_formed = form_module(index, other_index, tree, graph)
                if module_formed[0]:
                    if get_node_type(graph.subgraph(module_formed[1])) == tree[0].node_type and \
                            (tree[0].node_type==PARALLEL or tree[0].node_type==SERIES):
                        continue
                    return False
    return True

def get_node_type(graph):
    """
    Returns the module type of the root of modular decomposition tree of input graph

    INPUT:

    - ``graph`` -- Input sage graph

    OUTPUT:

    ``PRIME`` if graph is PRIME, ``PARALLEL`` if graph is PARALLEL and ``SERIES``
    if graph is of type SERIES

    """
    if not graph.is_connected():
        return PARALLEL
    elif graph.complement().is_connected():
        return PRIME
    return SERIES

def form_module(index, other_index, tree, graph):
    """
    This function forms a module out of the modules in the module pair. Let modules input be M1
    and M2. Let V be the set of vertices in these modules. Suppose x is a neighbor of subset of
    the vertices in V but not all the vertices and x does not belong to V. Then the set of
    modules also include the module which contains x. This process is repeated until a module
    is formed and the formed module if subset of V is returned.

    INPUT:

    - ``index`` -- First module in the module pair
    - ``other_index`` -- Second module in the module pair
    - ``tree`` -- Modular decomposition tree which contains the modules in the module pair
    - ``graph`` -- Graph whose modular decomposition tree is created

    OUTPUT:

    ``[module_formed, vertices]`` where ``module_formed`` is ``True`` if module is formed
    else ``False`` and ``vertices`` is a list of verices included in the formed module

    """
    vertices = set(get_vertices(tree[1][index]) + get_vertices(tree[1][other_index]))
    common_neighbors = set()    #stores all neighbors which are common for all vertices in V
    all_neighbors = set()   #stores all neighbors of vertices in V which are outside V
    flag = True
    while flag:
        all_neighbors = all_neighbors - set(vertices)
        common_neighbors = common_neighbors - set(vertices)
        for v in vertices:
            neighbor_list = set(graph.neighbors(v))
            neighbor_list = neighbor_list - vertices
            all_neighbors = all_neighbors | neighbor_list
            common_neighbors = common_neighbors & neighbor_list
        if all_neighbors == common_neighbors:   #indicates a module is formed
            flag = False
            if len(vertices) == graph.order():
                return [False, vertices]
            return [True, vertices]
        for v in (all_neighbors - common_neighbors):
            for index in range(len(tree[1])):
                if v in get_vertices(tree[1][index]):
                    vertices = vertices | set(get_vertices(tree[1][index]))
                    break

def test_module(module, graph):
    """
    Tests whether input module is actually a module

    INPUT:

    - ``module`` -- Module which needs to be tested
    - ``graph`` -- Input sage graph which contains the module

    OUTPUT:

    ``True`` if input module is a module by definition else ``False``

    """
    if module[0].node_type == NORMAL:
        return True
    vertices_in_module = get_vertices(module)
    vertices_outside = list(set(graph.vertices()) - set(vertices_in_module))

    #Nested module with only one child
    if module[0].node_type!=NORMAL and len(module[1])==1:
        return False
    #If children of SERIES module are all SERIES modules
    if module[0].node_type == SERIES:
        if children_node_type(module, SERIES):
            return False
    #If children of PARALLEL module are all PARALLEL modules
    if module[0].node_type == PARALLEL:
        if children_node_type(module, PARALLEL):
            return False
    #check the module by definition
    for v in vertices_outside:
        if not either_connected_or_not_connected(v, vertices_in_module, graph):
            return False
    return True

def children_node_type(module, node_type):
    """
    Tests whether node_type of children of node is same as input node_type

    INPUT:

    - ``module`` -- module which is tested
    - ``node_type`` -- input node_type

    OUTPUT:

    ``True`` if node_type of children of module is same as input node_type
    else ``False``

    """
    for tree in module[1]:
        if tree[0].node_type!=node_type:
            return False
    return True

def either_connected_or_not_connected(v, vertices_in_module, graph):
    """
    Test whether v is connected or disconnected to all vertices in the module

    INPUT:

    - ``v`` -- vertex tested
    - ``vertices_in_module`` -- list containing vertices in the module
    - ``graph`` -- graph to which the vertices belong

    OUTPUT:

    ``True`` if v is either connected or disconnected to all the vertices in
    the module else ``False``

    """

    #marks whether vertex v is connected to first vertex in the module
    connected = v in graph.neighbors(vertices_in_module[0])
    for u in vertices_in_module:
        if ((v in graph.neighbors(u)) != connected):
            return False
    return True

def number_components(root, vertex_status):
    """
    Function to number the components to the right of SOURCE vertex in the forest input to the
    assembly phase

    INPUT:

    - ``root`` -- the forest which contains the components and cocomponents
    - ``vertex_status`` -- dictionary which stores the position of vertex w.r.t SOURCE

    """
    comp_num = 0
    flag = False
    if not root:
        return ValueError("Input forest {} is empty".format(root))
    for tree in root[1]:
        if tree[0].node_type==NORMAL and vertex_status[tree[1][0]]==SOURCE:
            flag = True
            continue
        if not flag:    #Cocomponents are skipped
            continue
        comp_num += recursively_number_cocomponents(tree, comp_num, PARALLEL)

def number_cocomponents(root, vertex_status):
    """
    Function to number the cocomponents to the left of SOURCE vertex in the forest input to the
    assembly phase

    INPUT:

    - ``root`` -- the forest which contains the cocomponents and components
    - ``vertex_status`` -- dictionary which stores the position of vertex w.r.t SOURCE

    """
    cocomp_num = 0
    for tree in root[1]:
        #Only cocomponents are numbered
        if tree[0].node_type==NORMAL and vertex_status[tree[1][0]]==SOURCE:
            break
        cocomp_num += recursively_number_cocomponents(tree, cocomp_num, SERIES)

def recursively_number_cocomponents(tree, cocomp_num, by_type):
    """
    recursively numbers the nodes in the (co)components. If the tree node_type is same as
    by_type then cocomp_num is incremented before assigning to the subtree else entire
    tree is numbered by cocomp_num

    INPUT:

    - ``tree`` -- the forest which contains the cocomponents and components
    - ``cocomp_num`` -- input number to be used as reference for numbering the (co)components
    - ``by_type`` -- type which determines how numbering is done

    OUTPUT:

    The value incremented to ``cocomp_num``
    """
    orig_cocomp_num = cocomp_num

    #If node_type of tree is same as by_type then cocomp_num is incremented
    # for each subtree
    if tree[0].node_type==by_type:
        tree[0].comp_num = cocomp_num
        for subtree in tree[1]:
            number_subtree(subtree, cocomp_num)
            cocomp_num += 1
    else:
        number_subtree(tree, cocomp_num)
        cocomp_num+=1
    return cocomp_num - orig_cocomp_num

def number_subtree(tree, number):
    """
    sets the ``comp_num`` for all the nodes in the subtree to number

    INPUT:

    - ``tree`` -- tree to be numbered
    - ``number`` -- number assigned to the tree

    """
    tree[0].comp_num = number
    if tree[0].node_type!=NORMAL:
        for subtree in tree[1]:
            number_subtree(subtree, number)

def assembly(graph, root, vertex_status, vertex_dist):
    """
    It assembles the forest obtained after the promotion phase
    into a modular decomposition tree.

    INPUT:

    - ``graph`` -- graph whose MD tree is to be computed
    - ``root`` -- Forest which would be assembled into a MD tree
    - ``vertex_status`` -- Dictionary which stores the position of
                           vertex with respect to the source

    """
    mu = {}     #Maps index to the mu (co)component computed for the tree at the index
    source_index = -1   #Stores index of tree containing the source vertex in the forest

    # Maps index to list of vertices in the
    # tree at the index in the forest
    vertices_in_component = {}

    update_comp_num(root)
    for index, component in enumerate(root[1]):
        if component[0].node_type==NORMAL and vertex_status[component[1][0]]==SOURCE:
            source_index = root[1].index(component)
        vertices_in_component[index] = get_vertices(component)
        component[0].index_in_root = index

    #computes mu values for (co)components
    for index, component in enumerate(root[1]):
        if index < source_index:
            mu[index] = compute_mu_for_co_component(graph, index, source_index,
                                                    root, vertices_in_component)
        elif index > source_index:
            mu[index] = compute_mu_for_component(graph, index, source_index,
                                                 root, vertices_in_component)

    mu[source_index] = root[1][source_index]
    #stores the leftmost cocomponent included in the module containing source_index
    left = root[1][source_index]
    #stores the rightmost component included in the module containing source_index
    right = root[1][source_index]

    while not len(root[1])==1:
        #source_index is changed everytime a new module is formed therefore updated
        #left or right are changed every time module is formed
        #First series module is attempted
        [result, source_index] = check_series(root, left, right,
                                              source_index, mu)
        if result:
            left = root[1][source_index][1][0]
            continue

        #If series module cant be formed, parallel is tried
        [result, source_index] = check_parallel(graph, root, left, right,
                                                source_index, mu, vertex_dist,
                                                vertices_in_component)
        if result:
            right = root[1][source_index][1][-1]
            continue

        #Finally a prime module is formed if both series and parallel can not be created
        [result, source_index] = check_prime(graph, root, left, right,
                                             source_index, mu, vertex_dist,
                                             vertices_in_component)
        if result:
            if root[1][source_index][1][0][0].index_in_root != -1:
                left = root[1][source_index][1][0]
            if root[1][source_index][1][-1][0].index_in_root != -1:
                right = root[1][source_index][1][-1]

def update_comp_num(root):
    """
    Sets the comp_num of the parent to the comp_num of its first child

    INPUT:

    - ``root`` -- root of the tree whose nodes comp_num needs to be updated

    """
    if root[0].node_type!=NORMAL:
        root[0].comp_num = root[1][0][0].comp_num
        for tree in root[1]:
            update_comp_num(tree)

def check_prime(graph, root, left, right,
                source_index, mu, vertex_dist,
                vertices_in_component):
    """
    Assembles the forest to create a prime module.

    INPUT:

    - ``root`` - forest which needs to be assembled
    - ``left`` - The leftmost fragment of the last module
    - ``right`` - The rightmost fragment of the last module
    - ``source_index`` - index of the tree containing the source vertex
    - ``mu`` - dictionary which maps the (co)components with their mu values.

    OUTPUT:

    ``[module_formed, source_index]`` where ``module_formed`` is ``True`` if module is formed
    else ``False`` and ``source_index`` is the index of the new module which contains the
    source vertex

    """
    #stores the index of rightmost component included in the prime module
    new_right_index = source_index+1 if source_index+1 < len(root[1]) else source_index
    #stores the index of leftmost component included in the prime module
    new_left_index = source_index-1 if source_index-1 >= 0 else source_index
    #stores the indices of the cocomponents included in the prime module
    #the cocomponents are extracted one by one for adding more components
    left_queue = Queue()
    #stores the indices of the components included in the prime module
    #the components are extracted one by one for adding more cocomponents
    right_queue = Queue()

    if new_left_index != source_index:
        left_queue.put(new_left_index)
    if new_right_index != source_index:
        right_queue.put(new_right_index)

    while not left_queue.empty() or not right_queue.empty():
        if not left_queue.empty():
            #cocomponent indices extracted from the queue
            left_index = left_queue.get()
            #more components added based on the below condition
            while new_right_index < len(root[1]) - 1 and \
                            root[1][new_right_index][0].index_in_root < \
                            mu[left_index][0].index_in_root:
                new_right_index += 1
                right_queue.put(new_right_index)
            #cocomponent added while cocomponent at left_index
            #has cocomponent to its left with same comp_num
            while has_left_cocomponent_fragment(root, left_index):
                if left_index - 1 >= 0:
                    left_index -= 1
                    if new_left_index > left_index:
                        left_queue.put(left_index)
                    new_left_index = min(left_index, new_left_index)
        if not right_queue.empty():
            #component indices extracted from the queue
            right_index = right_queue.get()
            #more cocomponents added based on the below condition
            while new_left_index > 0 and \
                            root[1][new_left_index][0].index_in_root > \
                            mu[right_index][0].index_in_root:
                new_left_index -= 1
                left_queue.put(new_left_index)
            #component is added while component at right_index
            #has component to its right with same comp_num
            # or has a connected component with vertices at different
            #level from the source vertex
            while has_right_component_fragment(root, right_index) or \
                    has_right_layer_neighbor(graph, root, right_index,
                                             vertex_dist, vertices_in_component):
                if has_right_layer_neighbor(graph, root, right_index,
                                            vertex_dist, vertices_in_component):
                    new_left_index = 0
                    new_right_index = len(root[1]) - 1
                    break
                if right_index + 1 < len(root[1]):
                    right_index += 1
                    if new_right_index < right_index:
                        right_queue.put(right_index)
                    new_right_index = max(right_index, new_right_index)

    node = create_prime_node()
    #vertices or modules added in the prime_module
    for temp in range(new_left_index, new_right_index + 1):
        node[1].append(root[1][temp])
    # list elements included in the prime module
    # are removed from the forest
    root[1][new_left_index:new_right_index + 1] = []
    root[1].insert(new_left_index, node)
    return [True, new_left_index]

def check_parallel(graph, root, left, right,
                   source_index, mu, vertex_dist,
                   vertices_in_component):
    """
    Assembles the forest to create a parallel module.

    INPUT:

    - ``root`` -- forest which needs to be assembled
    - ``left`` -- The leftmost fragment of the last module
    - ``right`` -- The rightmost fragment of the last module
    - ``source_index`` -- index of the tree containing the source vertex
    - ``mu`` -- dictionary which maps the (co)components with their mu values.

    OUTPUT:

    ``[module_formed, source_index]`` where ``module_formed`` is ``True`` if module is formed
    else ``False`` and ``source_index`` is the index of the new module which contains the
    source vertex
    """

    #stores the index of rightmost component included in the parallel module
    new_right_index = source_index
    while new_right_index+1 < len(root[1]):
        #component at new_right_index + 1 is added only if it doesn't have
        # a component to its right with same comp_num
        if has_right_component_fragment(root, new_right_index+1):
            break
        #component at new_right_index + 1 is added only if it doesn't have a connected
        #component to its right with vertices at different level from its vertices
        if has_right_layer_neighbor(graph, root, new_right_index+1,
                                    vertex_dist, vertices_in_component):
            break
        #condition for adding more components in the parallel module
        if mu[root[1][new_right_index+1][0].index_in_root][0].index_in_root >= \
                left[0].index_in_root:
            new_right_index += 1
        else:
            break

    #if new_right_index > source_index then only parallel
    # module can be formed
    if source_index != new_right_index:
        node = create_parallel_node()
        temp = source_index
        for temp in range(source_index, new_right_index+1):
            #if module X to be included in the new parallel module Y
            # is also parallel then children of X are included in Y
            if root[1][temp][0].node_type == PARALLEL:
                for tree in root[1][temp][1]:
                    node[1].append(tree)
                    tree[0].index_in_root = root[1][temp][0].index_in_root
            else:
                node[1].append(root[1][temp])
        #list elements included in the parallel module
        # are removed from the forest
        root[1][source_index:new_right_index+1] = []
        root[1].insert(source_index, node)
        return [True, source_index]
    return [False, source_index]

def check_series(root, left, right, source_index, mu):
    """
    Assembles the forest to create a series module.

    - ``root`` -- forest which needs to be assembled
    - ``left`` -- The leftmost fragment of the last module
    - ``right`` -- The rightmost fragment of the last module
    - ``source_index`` -- index of the tree containing the source vertex
    - ``mu`` -- dictionary which maps the (co)components with their mu values.

    OUTPUT:

    ``[module_formed, source_index]`` where ``module_formed`` is ``True`` if module is formed
    else ``False`` and ``source_index`` is the index of the new module which contains the
    source vertex

    """

    #stores the index of leftmost component included in the parallel module
    new_left_index = source_index
    while new_left_index > 0:
        #cocomponent at new_left_index - 1 is added only if it doesn't have
        # a cocomponent to its left with same comp_num
        if has_left_cocomponent_fragment(root, new_left_index-1):
            break
        #condition for adding more cocomponents in the series module
        if mu[root[1][new_left_index-1][0].index_in_root][0].index_in_root <= \
                right[0].index_in_root:
            new_left_index -= 1
        else:
            break

    #if new_left_index < source_index then only series
    # module can be formed
    if source_index != new_left_index:
        node = create_series_node()
        for temp in range(new_left_index, source_index+1):
            if root[1][temp][0].node_type == SERIES:
                # if module X to be included in the new series module Y
                # is also series then children of X are included in Y
                for tree in root[1][temp][1]:
                    tree[0].index_in_root = root[1][temp][0].index_in_root
                    node[1].append(tree)
            else:
                node[1].append(root[1][temp])
        #list elements included in the series module
        # are removed from the forest
        root[1][new_left_index:source_index+1] = []
        root[1].insert(new_left_index, node)
        return [True, new_left_index]
    return [False, new_left_index]

def has_left_cocomponent_fragment(root, cocomp_index):
    """
    Returns True if cocomponent at  cocomp_index has a cocomponent
    to its left with same comp_num

    INPUT:

    - ``root`` -- The forest to which cocomponent belongs
    - ``cocomp_index`` -- Index at which cocomponent is present in root

    OUTPUT:

    ``True`` if cocomponent at  cocomp_index has a cocomponent
    to its left with same comp_num else ``False``
    """
    for index in range(cocomp_index):
        if root[1][index][0].comp_num == root[1][cocomp_index][0].comp_num:
            return True
    return False

def has_right_component_fragment(root, comp_index):
    """
    Returns True if component at  comp_index has a component
    to its right with same comp_num

    INPUT:

    - ``root`` -- The forest to which component belongs
    - ``comp_index`` -- Index at which component is present in root

    OUTPUT:

    ``True`` if component at  comp_index has a component
    to its right with same comp_num else ``False``
    """
    for index in range(comp_index+1, len(root[1])):
        if root[1][index][0].comp_num == root[1][comp_index][0].comp_num:
            return True
    return False

def has_right_layer_neighbor(graph, root, comp_index,
                             vertex_dist, vertices_in_component):
    """
    Returns True if component at  comp_index has a connected component
    to its right with vertices at different level from the source vertex

    INPUT:

    - ``root`` -- The forest to which component belongs
    - ``comp_index`` -- Index at which component is present in root

    OUTPUT:

    ``True`` if component at comp_index has a right layer neighbor
    else ``False``

    """
    for index in range(comp_index+1, len(root[1])):
        if vertex_dist[get_vertex_in(root[1][index])] > \
                vertex_dist[get_vertex_in(root[1][comp_index])] and \
                is_component_connected(graph, root[1][index][0].index_in_root,
                                       root[1][comp_index][0].index_in_root,
                                       vertices_in_component):
            return True
    return False

def get_vertex_in(tree):
    """
    Returns a vertex in the tree

    INPUT:

    - ``tree`` -- input modular decomposition tree

    OUTPUT:

    Returns the first vertex encountered in recursion
    """
    if tree[0].node_type==NORMAL:
        return tree[1][0]
    return get_vertex_in(tree[1][0])

def compute_mu_for_co_component(graph, component_index, source_index,
                                root, vertices_in_component):
    """
    Computes the mu value for co-component

    INPUT:

    - ``graph`` -- Graph whose MD tree needs to be computed
    - ``component_index`` -- index of the co-component
    - ``source_index`` -- index of the source in the forest
    - ``root`` -- the forest which needs to be assembled into a MD tree
    - ``vertices_in_component`` -- Dictionary which maps index i to list of
                                  vertices in the tree at index i in the forest

    OUTPUT:

    The mu value (component in the forest) for the co-component

    """

    #default mu value for a cocomponent
    mu_for_co_component = root[1][source_index]
    for index in range(len(root[1])-1, source_index, -1):
        if is_component_connected(graph, component_index,
                                  index, vertices_in_component):
            mu_for_co_component = root[1][index]
            return mu_for_co_component
    return mu_for_co_component

def compute_mu_for_component(graph, component_index, source_index,
                             root, vertices_in_component):
    """
    Computes the mu value for component

    INPUT:

    - ``graph`` -- Graph whose MD tree needs to be computed
    - ``component_index`` -- index of the component
    - ``source_index`` -- index of the source in the forest
    - ``root`` -- the forest which needs to be assembled into a MD tree
    - ``vertices_in_component`` -- Dictionary which maps index i to list of
                                  vertices in the tree at the index i in the forest

    OUTPUT:

    The mu value (co-component in the forest) for the component

    """

    #default mu value for a component
    mu_for_component = root[1][0]
    for index in range(0, source_index):
        if mu_for_component == root[1][index] and \
                is_component_connected(graph, component_index,
                                       index, vertices_in_component):
             mu_for_component = root[1][index+1]
    return mu_for_component

def is_component_connected(graph, index1, index2, vertices_in_component):
    """
    Returns True if two (co)components are connected else False

    INPUT:

    - ``graph`` -- Graph whose MD tree needs to be computed
    - ``index1`` -- index of the first (co)component
    - ``index2`` -- index of the second (co)component
    - ``vertices_in_component`` -- Dictionary which maps index i to list of
                                  vertices in the tree at the index i in the forest

    OUTPUT:

    ``True`` if the (co)components are connected else ``False``
    """
    vertices = vertices_in_component[index1]
    index2_vertices_set = set(vertices_in_component[index2])
    for vertex in vertices:
        neighbors = graph.neighbors(vertex)
        if not index2_vertices_set.isdisjoint(set(neighbors)):
            return True
    return False

def get_vertices(component):
    """
    Computes the list of vertices in the (co)component

    INPUT:

    - ``component`` -- (co)component whose vertices need to be returned as a list

    OUTPUT:

    list of vertices in the (co)component
    """
    vertices = []
    recurse_component(component, vertices)
    return vertices

def recurse_component(root, vertices):
    if root[0].node_type == NORMAL:
        vertices.append(root[1][0])
        return
    for tree in root[1]:
        recurse_component(tree, vertices)

def promote_left(root):
    """
    Performs the promotion phase on the forest root. If child and
    parent both are marked by LEFT_SPLIT then child is removed and
    placed just before the parent

    INPUT:

    - ``root`` -- The forest which needs to be promoted

    """
    q = Queue()
    #q has [parent, child] elements as parent needs to be modified
    for tree in root[1]:
        q.put([root, tree])

    while not q.empty():
        [parent, child] = q.get()
        if child[0].node_type==NORMAL:
            continue
        to_remove = []
        index = parent[1].index(child)
        for tree in child[1]:
            #if tree and child both have LEFT_SPLIT then tree from
            #child is inserted just before child in the parent
            if tree[0].has_left_split() and child[0].has_left_split():
                parent[1].insert(index, tree)
                index += 1
                to_remove.append(tree)
                q.put([parent, tree])
            else:
                q.put([child, tree])
        for tree in to_remove:
            child[1].remove(tree)

def promote_right(root):
    """
    Performs the promotion phase on the forest root. If child and
    parent both are marked by RIGHT_SPLIT then child is removed
    and placed just after the parent

    INPUT:

    - ``root`` -- The forest which needs to be promoted

    """
    q = Queue()
    #q has [parent, child] elements as parent needs to be modified
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        if child[0].node_type==NORMAL:
            continue
        to_remove = []
        index = parent[1].index(child)
        for tree in child[1]:
            #if tree and child both have RIGHT_SPLIT then tree from
            #child is inserted just after child in the parent
            if tree[0].has_right_split() and child[0].has_right_split():
                parent[1].insert(index+1, tree)
                to_remove.append(tree)
                q.put([parent, tree])
            else:
                q.put([child, tree])
        for tree in to_remove:
                child[1].remove(tree)

def promote_child(root):
    """
    Performs the promotion phase on the forest `root`. If marked parent
    has no children it is removed, if it has one child then it is
    replaced by its child

    INPUT:

    - ``root`` -- The forest which needs to be promoted

    """
    q = Queue()
    #q has [parent, child] elements as parent needs to be modified
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        if child[0].node_type==NORMAL:
            continue
        #if child node itself have only one child
        if len(child[1])==1 and (child[0].node_split!=NO_SPLIT or
                                         child[0].node_type==FOREST):
            tree = child[1][0]
            index = parent[1].index(child)
            parent[1].insert(index, tree)
            parent[1].remove(child)
            q.put([parent, tree])
        #if child node has no children
        elif ((not child[1]) and child[0].node_split!=NO_SPLIT):
            parent[1].remove(child)
        else:
            for tree in child[1]:
                    q.put([child, tree])

def clear_node_split_info(root):
    """
    sets the node_split of nodes to NO_SPLIT

    INPUT:

    - ``root`` -- The forest which needs to be cleared of split information

    """

    root[0].node_split = NO_SPLIT
    if root[0].node_type!=NORMAL:
        for subroot in root[1]:
            clear_node_split_info(subroot)

def refine(graph, root, vertex_dist, vertex_status):
    """
    refines the forest based on the active edges

    INPUT:

    - ``graph`` -- graph whose MD tree needs to be computed
    - ``root`` -- the forest which needs to be assembled into a MD tree
    - ``vertex_dist`` -- dictionary mapping the vertex with distance from the source
    - ``vertex_status`` -- dictionary mapping the vertex to the position w.r.t source

    """
    x_used = []
    #active edges of each vertex in the graph is used to refine the forest
    for v in graph.vertices():
        if v in vertex_status and vertex_status[v] == SOURCE:
            continue
        x = []     #list of vertices connected through active edges to v
        for e in graph.edges_incident(v):
            if vertex_dist[e[0]] != vertex_dist[e[1]]:
                x.append(e[0] if e[0]!=v else e[1])
        if set(x) not in x_used:
            x_used.append(set(x))
            maximal_subtrees_with_leaves_in_x(root, v, x, vertex_status, False, 0)
    get_child_splits(root)

def get_child_splits(root):
    """
    Adds the node_split of children to the parent node

    INPUT:

    - ``root`` -- input modular decomposition tree

    """
    if root[0].node_type!=NORMAL:
        for tree in root[1]:
            get_child_splits(tree)
            root[0].set_node_split(tree[0].node_split)

def maximal_subtrees_with_leaves_in_x(root, v, x, vertex_status,
                                      tree_left_of_source, level):
    """
    Refines the forest based on the active edges(x) of vertex v

    INPUT:

    - ``root`` -- the forest which needs to be assembled into a MD tree
    - ``v`` -- the vertex used to refine
    - ``x`` -- list of vertices connected to v and at different distance
               from source compared to v
    - ``vertex_status`` -- dictionary mapping the vertex to the position w.r.t source
    - ``tree_left_of_source`` -- flag indicating whether tree is
    - ``level`` -- indicates the recursion level, 0 for root

    """
    return_split = NO_SPLIT
    #all trees in a forest are refined using x
    if root[0].node_type == FOREST:
        left_flag = True    #indicates whether tree is left of source, True if left of source
        for tree in root[1]:
            if tree[0].node_type == NORMAL and tree[1][0] in vertex_status \
                    and vertex_status[tree[1][0]] == SOURCE:
                left_flag = False
            subtree_result = maximal_subtrees_with_leaves_in_x(tree, v, x, vertex_status,
                                                               left_flag, level)
            if subtree_result:
                #Mark the ancestors
                root[0].set_node_split(subtree_result[1])
    #handles the prime, series and parallel cases
    elif root[0].node_type != NORMAL:
        flag = True   #indicates the entire root is contained in x
        split_flag = False  #indicates a split is required
        Ta = []  # contains subtrees with leaves in x
        Tb = []  # contains subtrees with leaves not in x
        for subtree in root[1]:
            #refines the children of root
            subtree_result = maximal_subtrees_with_leaves_in_x(subtree, v, x, vertex_status,
                                                               tree_left_of_source, level+1)
            if subtree_result:
                flag = flag and subtree_result[0]

                #adds the node split of children to root
                root[0].set_node_split(subtree_result[1])

                if subtree_result[0]:
                    Ta.append(subtree)
                    split_flag = True
                else:
                    Tb.append(subtree)
        if root[0].node_type == PRIME:
            # mark all the children of prime nodes
            for prime_subtree in root[1]:
                prime_subtree[0].set_node_split(root[0].node_split)
        if flag:
            #return if all subtrees are in x, no split required
            return [True, root[0].node_split]
        elif split_flag:    #split required`
            split = LEFT_SPLIT
            #if v is right of source and tree is also right of source then RIGHT_SPLIT
            if vertex_status[v] == RIGHT_OF_SOURCE and not tree_left_of_source:
                split = RIGHT_SPLIT

            #add the split to root node_split
            root[0].set_node_split(split)

            if root[0].node_type == PRIME:
                #mark all the children of prime nodes
                for subtree in root[1]:
                    subtree[0].set_node_split(split)
                return [False, split]

            if root[0].is_separated:
                #if root has already been split then
                # further split not required
                return [flag, root[0].node_split]
            #Add nodes for both Ta and Tb
            node_type = root[0].node_type
            root[0].is_separated = True
            root[1] = []

            #add two nodes for Ta and Tb
            root[1].append(create_parallel_node())
            root[1][-1][0].node_type = node_type
            root[1][-1][0].node_split = root[0].node_split
            root[1].append(create_parallel_node())
            root[1][-1][0].node_type = node_type
            root[1][-1][0].node_split = root[0].node_split
            root[1][-2][1] = Ta
            root[1][-1][1] = Tb
            root[1][-2][0].comp_num = Ta[0][0].comp_num
            root[1][-1][0].comp_num = Tb[0][0].comp_num

        return_split = root[0].node_split
        return [flag, return_split]
    elif root[1][0] in x:
        return [True, root[0].node_split]
    else:
        return [False, root[0].node_split]

def create_prime_node():
    return [NodeInfo(PRIME), []]

def create_parallel_node():
    return [NodeInfo(PARALLEL), []]

def create_series_node():
    return [NodeInfo(SERIES), []]

def create_normal_node(vertex):
    return [NodeInfo(NORMAL), [vertex]]

def print_md_tree(root,level):
    if root[0].node_type!=NORMAL:
        print "  "*level+str(root[0])
        for tree in root[1]:
            print_md_tree(tree,level+1)
    else:
        print "  "*level+str(root[1][0])
