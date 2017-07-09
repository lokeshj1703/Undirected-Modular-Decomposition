from sage.all import Graph
from sage.graphs.generators.smallgraphs import HallJankoGraph
from sage.graphs.generators.smallgraphs import ChvatalGraph
from sage.graphs.generators.smallgraphs import DesarguesGraph
from sage.graphs.generators.smallgraphs import FlowerSnark
from sage.graphs.generators.smallgraphs import FruchtGraph
from sage.graphs.generators.smallgraphs import HeawoodGraph
from sage.graphs.generators.smallgraphs import MoebiusKantorGraph
from sage.graphs.generators.smallgraphs import PappusGraph
from sage.graphs.generators.smallgraphs import PetersenGraph
from sage.graphs.generators.smallgraphs import ThomsenGraph
from sage.graphs.generators.basic import CycleGraph
from sage.graphs.generators.platonic_solids import TetrahedralGraph
from sage.graphs.generators.platonic_solids import DodecahedralGraph
from sage.graphs.generators.platonic_solids import OctahedralGraph
from sage.graphs.generators.platonic_solids import IcosahedralGraph
from sage.graphs.generators.platonic_solids import HexahedralGraph
from sage.graphs.generators.families import DorogovtsevGoltsevMendesGraph
from sage.graphs.generators.families import BalancedTree
from sage.graphs.generators.basic import CircularLadderGraph
from sage.graphs.generators.families import CubeGraph
#from queue import Queue

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
    """

    def __init__(self, node_type):
        self.node_type = node_type
        self.node_split = NO_SPLIT
        self.index_in_root = -1
        self.comp_num = -1
        self.is_separated = False

    def set_node_split(self, node_split):
        if self.node_split == NO_SPLIT:
            self.node_split = node_split
        elif ((self.node_split == LEFT_SPLIT and node_split == RIGHT_SPLIT) or
              (self.node_split == RIGHT_SPLIT and node_split == LEFT_SPLIT)):
            self.node_split = BOTH_SPLIT

    def has_left_split(self):
        return self.node_split==LEFT_SPLIT or self.node_split==BOTH_SPLIT

    def has_right_split(self):
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
        string += "  "
        if self.node_split==LEFT_SPLIT:
            string += "LEFT"
        elif self.node_split==RIGHT_SPLIT:
            string += "RIGHT"
        elif self.node_split==BOTH_SPLIT:
            string += "BOTH"

        string += " c" + str(self.comp_num)
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

    :param graph: The graph for which modular decompostion
                  tree needs to be computed
    :return: Modular decomposition tree computed for the graph
    """
    #print graph.vertices()
    if graph._directed:
        return ValueError("Graph must be undirected")
    if graph.order() == 1:         #Single vertex graph
        root = create_normal_node(next(graph.vertex_iterator()))
        #print root
        return root
    if not graph.is_connected():
        #Parallel case:- The tree contains the MD trees
        # of its connected components as subtrees
        components = graph.connected_components()
        root = create_parallel_node()
        for component in components:
            root[1].append(modular_decomposition(graph.subgraph(component)))
        #print root
        return root
    elif graph.complement().is_connected():
        root = create_prime_node()
    else:
        root = create_series_node()
    #print next(graph.vertex_iterator())
    bfs_generator = graph.breadth_first_search(next(graph.vertex_iterator()), report_distance=True)
    prev_level_distance = -1    #used as a demarker for different levels in bfs
    prev_level_list = []    #stores the vertices in previous level
    vertex_dist = {}        #dictionary stores the distance of vertices from the SOURCE
    vertex_status = {}      #dictionary stores the position of vertices w.r.t SOURCE
    vertex_status[next(graph.vertex_iterator())] = SOURCE
    for (vertex, distance) in bfs_generator:
        vertex_dist[vertex] = distance
        #print "vertex_dist", vertex, vertex_dist[vertex]
        #Different distances from the source vertex are considered
        # as different levels in the algorithm
        if distance != prev_level_distance: #On start of new level in BFS
            if prev_level_list:
                #print "recursive call",prev_level_list
                #MD Tree is computed for each level and added to the forest
                root[1].append(modular_decomposition(graph.subgraph(prev_level_list)))
            if prev_level_distance==1 and distance!=1:
                #Mark the neighbours of source as LEFT_OF_SOURCE
                # as they appear to left of source in the forest
                # other vertices are marked as RIGHT_OF_SOURCE
                for v in prev_level_list:
                    vertex_status[v] = LEFT_OF_SOURCE
            elif prev_level_distance!=0:
                for v in prev_level_list:
                    vertex_status[v] = RIGHT_OF_SOURCE
            prev_level_list = []
            prev_level_distance = distance
        prev_level_list.append(vertex)

    #The last level is left out in the above loop
    if distance == 1:
        for v in prev_level_list:
            vertex_status[v] = LEFT_OF_SOURCE
    elif distance != 0:
        for v in prev_level_list:
            vertex_status[v] = RIGHT_OF_SOURCE
    #print "recursive call", prev_level_list
    root[1].append(modular_decomposition(graph.subgraph(prev_level_list)))

    #The MD tree for the neighbours of source marked as LEFT_OF_SOURCE
    # are placed left of Source in the forest. root[1][1] is the source
    # and root[1][0] is the MD tree for the neighbours
    temp = root[1][1]
    root[1][1] = root[1][0]
    root[1][0] = temp
    root[0].node_type = FOREST
    #print root
    #print "************REFINEMENT************"
    #print "vertex_status: ", vertex_status
    clear_node_split_info(root)
    number_cocomponents(root, vertex_status)
    number_components(root, vertex_status)
    #print root
    refine(graph, root, vertex_dist, vertex_status)
    #print "************PROMOTE LEFT**********"
    promote_left(root)
    #print "************PROMOTE RIGHT************"
    promote_right(root)
    #print "************PROMOTE CHILD************"
    promote_child(root)
    assembly(graph, root, vertex_status, vertex_dist)
    #print root
    if root[0].node_type==FOREST:
        return root[1][0]
    else:
        return root

def test_modular_decomposition(tree, graph):
    """
    This function that tests the modular decomposition tree using recursion.
    :param tree: Modular decomposition tree to be tested
    :param graph: Graph whose modular decomposition tree needs to be tested
    :return returns True if it is a modular decomposition
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
    (M1, M2), (M1, M3), ...(M1, Mn); (M2, M3), (M2, M4), ...(M2, Mn);... and so on and tries to form
    a module using the pair. If the module formed has same type as M and is of type SERIES or
    PARALLEL then the formed module is not considered maximal. Otherwise it is considered maximal
    and M is not a modular decomposition tree.
    :param tree: Modular decomposition tree whose modules are tested for maximal nature
    :param graph: Graph whose modular decomposition tree is tested
    :return returns True if all modules at first level in the modular ddecomposition tree are
            maximal in nature
    """
    if tree[0].node_type!=NORMAL:
        for index, module in enumerate(tree[1]):
            for other_index in range(index+1, len(tree[1])):
                #print index, other_index
                module_formed = form_module(index, other_index, tree, graph)
                if module_formed[0]:
                    if get_node_type(graph.subgraph(module_formed[1])) == tree[0].node_type and \
                                    tree[0].node_type==PARALLEL or tree[0].node_type==SERIES:
                        continue
                    return False
    return True
    """for other_module in tree[1]:
        if other_module != module:
            new_module = list(set(module) + set(other_module))"""

def get_node_type(graph):
    """
    Returns the module type of the root of modular decomposition tree of graph
    :param graph: Input sage graph
    """
    if not graph.is_connected():
        return PARALLEL
    elif graph.complement().is_connected():
        return PRIME
    return SERIES

def form_module(index, other_index, tree, graph):
    """
    This function forms a module out of the modules in the module pair. Let modules input be M1
    and M2. Let V be the set of vertices in these modules. Suppose x is a neighbor outside V of
    of subset of the vertices in V but not all the vertices. Then the set of modules also
    include the module which contains x. This process is repeated until a module is formed and
    and the formed module if subset of V is returned.
    :param index: First module in the module pair
    :param other_index: Second module in the module pair
    :param tree: Modular decomposition tree which contains the modules in the module pair
    :param graph: Graph whose modular decomposition tree is created
    :return: returns a list containing boolean signifying whether a module is formed and
             a list of vertices in the module
    """
    vertices = set(get_vertices(tree[1][index])+get_vertices(tree[1][other_index]))
    #print vertices,get_vertices(tree[1][index])
    #print tree[1][index],tree[1][other_index]
    common_neighbors = set()    #stores all neighbors which are common for all vertices in V
    all_neighbors = set()   #stores all neighbors of vertices in V which are outside V
    flag = True
    while flag:
        #print vertices
        all_neighbors = all_neighbors - set(vertices)
        common_neighbors = common_neighbors - set(vertices)
        for v in vertices:
            neighbor_list = set(graph.neighbors(v))
            neighbor_list = neighbor_list - vertices
            all_neighbors = all_neighbors | neighbor_list
            common_neighbors = common_neighbors & neighbor_list
        if all_neighbors==common_neighbors:
            flag = False
            if len(vertices)==graph.order():
                return [False,vertices]
            return [True,vertices]
        for v in (all_neighbors-common_neighbors):
            for index in range(len(tree[1])):
                #print index, tree[1][index]
                if v in get_vertices(tree[1][index]):
                    vertices = vertices | set(get_vertices(tree[1][index]))
                    break

def test_module(module, graph):
    """
    Tests whether input module is actually a module.
    :param module: Module which needs to be tested
    :param graph: Input sage graph which contains the module
    """
    if module[0].node_type==NORMAL:
        return True
    vertices_in_module = get_vertices(module)
    vertices_outside = list(set(graph.vertices()) - set(vertices_in_module))
    if module[0].node_type!=NORMAL and len(module[1])==1:
        return False
    if module[0].node_type==SERIES:
        if children_node_type(module, SERIES):
            return False
    if module[0].node_type==PARALLEL:
        if children_node_type(module, PARALLEL):
            return False
    for v in vertices_outside:
        if not either_connected_or_not_connected(v, vertices_in_module, graph):
            return False
    return True

def children_node_type(module, node_type):
    """
    Tests whether node_type of children of node is same as input node_type
    :param module: module which is tested
    :param node_type: input node_type
    :return: returns True if node_type of children of module is same as input node_type
    """
    for tree in module[1]:
        if tree[0].node_type!=node_type:
            return False
    return True

def either_connected_or_not_connected(v, vertices_in_module, graph):
    """
    Test whether v is connected or disconnected to all vertices in the module
    :param v: vertex tested
    :param vertices_in_module: list containing vertices in the module
    :param graph: graph to which the vertices belong
    :return:
    """
    #marks whether vertex v is connected to first vertex in the module
    connected = v in graph.neighbors(vertices_in_module[0])
    #print "v: ", v, "connected ", connected
    for u in vertices_in_module:
        #print "u: ",u,v in graph.neighbors(u)
        if ((v in graph.neighbors(u)) != connected):
            #print "NOPE"
            return False
    return True

def number_components(root, vertex_status):
    """
    Function to number the components to the right of SOURCE vertex in the forest input to the
    assembly phase
    :param root: the forest which contains the components and cocomponents
    :param vertex_status: dictionary which stores the position of vertex w.r.t SOURCE
    """
    comp_num = 0
    flag = False
    if not root:
        return ValueError("Input forest {} is empty".format(root))
    for tree in root[1]:
        #print tree
        if tree[0].node_type==NORMAL and vertex_status[tree[1][0]]==SOURCE:
            flag = True
            continue
        if not flag:
            continue
        comp_num += recursively_number_cocomponents(tree, comp_num, PARALLEL)

def number_cocomponents(root, vertex_status):
    """
    Function to number the cocomponents to the left of SOURCE vertex in the forest input to the
    assembly phase
    :param root: the forest which contains the cocomponents and components
    :param vertex_status: dictionary which stores the position of vertex w.r.t SOURCE
    """
    cocomp_num = 0
    for tree in root[1]:
        #print tree
        if tree[0].node_type==NORMAL and vertex_status[tree[1][0]]==SOURCE:
            break
        cocomp_num += recursively_number_cocomponents(tree, cocomp_num, SERIES)

def recursively_number_cocomponents(tree, cocomp_num, by_type):
    """
    recursively numbers the nodes in the (co)components. If the tree node_type is same as
    by_type then cocomp_num is incremented before assigning to the subtree else entire
    tree is numbered by cocomp_num
    :param tree: the forest which contains the cocomponents and components
    :param cocomp_num: input number to be used as reference for numbering the (co)components
    :param by_type: type which determines how numbering is done
    :return: The value incremented to cocomp_num
    """
    orig_cocomp_num = cocomp_num
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
    number the subtree by number
    :param tree: tree to be numbered
    :param number: number assigned to the tree
    """
    tree[0].comp_num = number
    if tree[0].node_type!=NORMAL:
        for subtree in tree[1]:
            number_subtree(subtree, number)

def assembly(graph, root, vertex_status, vertex_dist):
    """
    It assembles the forest obtained after the promotion phase
    into a modular decomposition tree.

    :param graph: graph whose MD tree is to be computed
    :param root: Forest which would be assembled into a MD tree
    :param vertex_status: Dictionary which stores the position of
                          vertex with respect to the source
    """
    #print "***********ASSEMBLY**************"
    mu = {}     #Maps index to the mu (co)component computed for the tree at the index
    source_index = -1   #Stores index of tree containing the source vertex in the forest

    # Maps index to list of vertices in the
    # tree at the index in the forest
    vertices_in_component = {}

    # Maps index to boolean indicating whether a component at
    # the index is connected to a component to its right
    component_at_index = {}     #Maps index to tree at that index in the forest `root`

    update_comp_num(root)
    for index, component in enumerate(root[1]):
        component_at_index[index] = component
        if component[0].node_type==NORMAL and vertex_status[component[1][0]]==SOURCE:
            source_index = root[1].index(component)
        vertices_in_component[index] = get_vertices(component)
        root[1][index][0].index_in_root = index

    for index, component in enumerate(root[1]):
        if index < source_index:
            mu[index] = compute_mu_for_co_component(graph, index, source_index, root, vertices_in_component)
        elif index > source_index:
            mu[index] = compute_mu_for_component(graph, index, source_index, root, vertices_in_component)

    mu[source_index] = root[1][source_index]
    #print mu
    #print vertices_in_component
    #print component_at_index
    left = root[1][source_index]
    right = root[1][source_index]
    while not len(root[1])==1:
        #print "ROOT: ",root
        #source_index is changed everytime a new module is formed therefore updated
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
    if root[0].node_type!=NORMAL:
        root[0].comp_num = root[1][0][0].comp_num
        for tree in root[1]:
            update_comp_num(tree)

def check_prime(graph, root, left, right, source_index, mu, vertex_dist, vertices_in_component):
    """
    Assembles the forest to create a prime module.

    :param root: forest which needs to be assembled
    :param left: The leftmost fragment of the last module
    :param right: The rightmost fragment of the last module
    :param source_index: index of the tree containing the source vertex
    :param mu: dictionary which maps the (co)components with their mu values.
    :return list containing flag and the new source_index. flag if True indicates
            a module was formed.
    """
    new_right_index = source_index+1 if source_index+1 < len(root[1]) else source_index
    new_left_index = source_index-1 if source_index-1 >=0 else source_index
    right_index_for_mu = new_right_index
    left_index_for_mu = new_left_index
    """while new_left_index>=0:
        while new_right_index<len(root[1])-1 and \
                        root[1][new_right_index][0].index_in_root < mu[new_left_index][0].index_in_root:
            new_right_index += 1
        new_left_index-=1"""
    left_queue = Queue()
    right_queue = Queue()
    if new_left_index!=source_index:
        left_queue.put(new_left_index)
    if new_right_index!=source_index:
        right_queue.put(new_right_index)
    #print "$$$$$$OK$$$$$"
    while not left_queue.empty() or not right_queue.empty():
        if not left_queue.empty():
            """if new_left_index==0:
                left_queue.clear()
                continue"""
            left_index = left_queue.get()
            #print "LEFT_INDEX: ", left_index
            while new_right_index < len(root[1]) - 1 and \
                            root[1][new_right_index][0].index_in_root < mu[left_index][0].index_in_root:
                new_right_index += 1
                right_queue.put(new_right_index)
            while has_left_cocomponent_fragment(root, left_index):
                #print "LEFT_COCOMP: "+str(left_index)
                if left_index-1>=0:
                    left_index-=1
                    if new_left_index>left_index:
                        left_queue.put(left_index)
                    new_left_index = min(left_index, new_left_index)
        if not right_queue.empty():
            """if new_right_index==len(root[1])-1:
                right_queue.clear()
                continue"""
            right_index = right_queue.get()
            #print "RIGHT_INDEX: ",right_index
            while new_left_index > 0 and \
                            root[1][new_left_index][0].index_in_root > mu[right_index][0].index_in_root:
                new_left_index -= 1
                left_queue.put(new_left_index)
            while has_right_component_fragment(root, right_index) or \
                    has_right_layer_neighbor(graph, root, right_index, vertex_dist, vertices_in_component):
                if has_right_layer_neighbor(graph, root, right_index, vertex_dist, vertices_in_component):
                    new_left_index = 0
                    new_right_index = len(root[1])-1
                    break
                if right_index + 1 < len(root[1]):
                    right_index += 1
                    if new_right_index<right_index:
                        right_queue.put(right_index)
                    new_right_index = max(right_index, new_right_index)
    """if left_index_for_mu != source_index:
        if new_right_index<len(root[1])-1 and \
                        root[1][new_right_index][0].index_in_root < mu[new_left_index][0].index_in_root:
            new_right_index += 1
    if right_index_for_mu != source_index:
        if new_left_index>0 and \
                        root[1][new_left_index][0].index_in_root > mu[right_index_for_mu][0].index_in_root:
            new_left_index -= 1"""
    node = create_prime_node()
    for temp in range(new_left_index, new_right_index+1):
        node[1].append(root[1][temp])
    #print "PRIME Indices", new_left_index, new_right_index
    root[1][new_left_index:new_right_index + 1] = []
    root[1].insert(new_left_index, node)
    return [True, new_left_index]

def check_parallel(graph, root, left, right, source_index, mu, vertex_dist, vertices_in_component):
    """
    Assembles the forest to create a parallel module.

    :param root: forest which needs to be assembled
    :param left: The leftmost fragment of the last module
    :param right: The rightmost fragment of the last module
    :param source_index: index of the tree containing the source vertex
    :param mu: dictionary which maps the (co)components with their mu values.
    :return list containing flag and the new source_index. flag if True indicates
            a module was formed.

    """
    new_right_index = source_index
    while new_right_index+1 < len(root[1]):
        if has_right_component_fragment(root, new_right_index+1):
            break
        if has_right_layer_neighbor(graph, root, new_right_index+1, vertex_dist, vertices_in_component):
            break
        if mu[root[1][new_right_index+1][0].index_in_root][0].index_in_root >= left[0].index_in_root:
            new_right_index += 1
        else:
            break
    if source_index != new_right_index:
        node = create_parallel_node()
        temp = source_index
        for temp in range(source_index, new_right_index+1):
            if root[1][temp][0].node_type == PARALLEL:
                for tree in root[1][temp][1]:
                    node[1].append(tree)
                    tree[0].index_in_root = root[1][temp][0].index_in_root
            else:
                node[1].append(root[1][temp])
        root[1][source_index:new_right_index+1] = []
        root[1].insert(source_index, node)
        return [True, source_index]
    return [False, source_index]

def check_series(root, left, right, source_index, mu):
    """
    Assembles the forest to create a series module.

    :param root: forest which needs to be assembled
    :param left: The leftmost fragment of the last module
    :param right: The rightmost fragment of the last module
    :param source_index: index of the tree containing the source vertex
    :param mu: dictionary which maps the (co)components with their mu values.
    :return list containing flag and the new source_index. flag if True indicates
            a module was formed.

    """
    new_left_index = source_index
    while new_left_index > 0:
        if has_left_cocomponent_fragment(root, new_left_index-1):
            break
        if mu[root[1][new_left_index-1][0].index_in_root][0].index_in_root <= right[0].index_in_root:
            new_left_index -= 1
        else:
            break
    if source_index != new_left_index:
        node = create_series_node()
        for temp in range(new_left_index, source_index+1):
            if root[1][temp][0].node_type == SERIES:
                for tree in root[1][temp][1]:
                    node[1].append(tree)
                    tree[0].index_in_root = root[1][temp][0].index_in_root
            else:
                node[1].append(root[1][temp])
        root[1][new_left_index:source_index+1] = []
        root[1].insert(new_left_index, node)
        return [True, new_left_index]
    return [False, new_left_index]

def has_left_cocomponent_fragment(root, cocomp_index):
    for index in range(cocomp_index):
        if root[1][index][0].comp_num == root[1][cocomp_index][0].comp_num:
            return True
    return False

def has_right_component_fragment(root, comp_index):
    for index in range(comp_index+1, len(root[1])):
        if root[1][index][0].comp_num == root[1][comp_index][0].comp_num:
            return True
    return False

def has_right_layer_neighbor(graph, root, comp_index, vertex_dist, vertices_in_component):
    for index in range(comp_index+1, len(root[1])):
        if vertex_dist[get_vertex_in(root[1][index])] > vertex_dist[get_vertex_in(root[1][comp_index])] and \
                is_component_connected(graph, root[1][index][0].index_in_root, root[1][comp_index][0].index_in_root, vertices_in_component):
            return True
    return False

def get_vertex_in(tree):
    if tree[0].node_type==NORMAL:
        return tree[1][0]
    return get_vertex_in(tree[1][0])

def compute_mu_for_co_component(graph, component_index, source_index, root, vertices_in_component):
    """
    Computes the mu value for co-component

    :param graph: Graph whose MD tree needs to be computed
    :param component_index: index of the co-component
    :param source_index: index of the source in the forest
    :param root: the forest which needs to be assembled into a MD tree
    :param vertices_in_component: Dictionary which maps index to list of
                                  vertices in the tree at the index in the forest
    :return: The mu value (component in the forest) for the co-component
    """
    mu_for_co_component = root[1][source_index]
    for index in range(len(root[1])-1, source_index, -1):
        if is_component_connected(graph, component_index, index, vertices_in_component):
            mu_for_co_component = root[1][index]
            return mu_for_co_component
    return mu_for_co_component

def is_left_connected(graph, component_index, root, vertices_in_component):
    """
    Returns a connected component to the right of the input component

    :param graph: Graph whose MD tree needs to be computed
    :param component_index: index of the co-component
    :param source_index: index of the source in the forest
    :param root: the forest which needs to be assembled into a MD tree
    :param vertices_in_component: Dictionary which maps index to list of
                                  vertices in the tree at the index in the forest
    :return: Component connected to the component at the component_index
    """
    for index in range(component_index):
        if is_component_connected(graph, component_index, index, vertices_in_component):
            return True
    return False

def get_right_connected(graph, component_index, source_index, root, vertices_in_component):
    """
    Returns a connected component to the right of the input component

    :param graph: Graph whose MD tree needs to be computed
    :param component_index: index of the co-component
    :param source_index: index of the source in the forest
    :param root: the forest which needs to be assembled into a MD tree
    :param vertices_in_component: Dictionary which maps index to list of
                                  vertices in the tree at the index in the forest
    :return: Component connected to the component at the component_index
    """
    for index in range(source_index+1, len(root[1])):
        if is_component_connected(graph, component_index, index, vertices_in_component):
            return root[1][index-1]
    return root[1][len(root[1])-1]

def compute_mu_for_component(graph, component_index, source_index, root, vertices_in_component):
    """
    Computes the mu value for component

    :param graph: Graph whose MD tree needs to be computed
    :param component_index: index of the component
    :param source_index: index of the source in the forest
    :param root: the forest which needs to be assembled into a MD tree
    :param vertices_in_component: Dictionary which maps index to list of
                                  vertices in the tree at the index in the forest
    :return: The mu value (co-component in the forest) for the component
    """
    mu_for_component = root[1][0]
    for index in range(0, source_index):
        if is_component_connected(graph, component_index, index, vertices_in_component):
             mu_for_component = root[1][index+1]
    return mu_for_component

def is_component_connected(graph, index1, index2, vertices_in_component):
    """
    Determines whether two (co)components are connected or not
    :param graph: Graph whose MD tree needs to be computed
    :param index1: index of the first (co)component
    :param index2: index of the second (co)component
    :param vertices_in_component: Dictionary which maps index to list of
                                  vertices in the tree at the index in the forest
    :return: True if the (co)components are connected else False
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
    Computes the list of vertices in the component

    :param component: component whose vertices need to be returned as a list
    :return: list of vertices in the component
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
    Performs the promotion phase on the forest `root`
    :param root: The forest which needs to be promoted

    If child and parent both are marked by LEFT_SPLIT then child
    is removed and placed just before the parent
    """
    q = Queue()
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        #print "parent=",parent
        #print "child =",child
        if child[0].node_type==NORMAL:
            continue
        to_remove = []
        index = parent[1].index(child)
        for tree in child[1]:
            #print tree[0].has_left_split(), child[0].has_left_split()
            if tree[0].has_left_split() and child[0].has_left_split():
                parent[1].insert(index, tree)
                index += 1
                to_remove.append(tree)
                q.put([parent, tree])
            else:
                q.put([child, tree])
        for tree in to_remove:
            child[1].remove(tree)
    #print root

def promote_right(root):
    """
    Performs the promotion phase on the forest `root`
    :param root: The forest which needs to be promoted

    If child and parent both are marked by RIGHT_SPLIT then child
    is removed and placed just after the parent
    """
    q = Queue()
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        #print "parent=",parent
        #print "child =",child
        if child[0].node_type==NORMAL:
            continue
        to_remove = []
        index = parent[1].index(child)
        for tree in child[1]:
            if tree[0].has_right_split() and child[0].has_right_split():
                parent[1].insert(index+1, tree)
                #index += 1
                to_remove.append(tree)
                q.put([parent, tree])
            else:
                q.put([child, tree])
        for tree in to_remove:
                child[1].remove(tree)
    #print root

def promote_child(root):
    """
    Performs the promotion phase on the forest `root`
    :param root: The forest which needs to be promoted

    If marked parent has no children it is removed, if it has one
    child then it is replaced by its child
    """
    q = Queue()
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        #print "parent=",parent
        #print "child =",child
        if child[0].node_type==NORMAL:
            continue
        if len(child[1])==1 and (child[0].node_split!=NO_SPLIT or child[0].node_type==FOREST):
            tree = child[1][0]
            index = parent[1].index(child)
            parent[1].insert(index, tree)
            parent[1].remove(child)
            q.put([parent, tree])
        elif ((not child[1]) and child[0].node_split!=NO_SPLIT):
            parent[1].remove(child)
        else:
            for tree in child[1]:
                    q.put([child, tree])
    #print root

def clear_node_split_info(root):
    """
    Clears the nodes of any split marks

    :param root: The forest which needs to be cleared

    """

    root[0].node_split = NO_SPLIT
    if root[0].node_type!=NORMAL:
        for subroot in root[1]:
            clear_node_split_info(subroot)

def refine(graph, root, vertex_dist, vertex_status):
    """
    refines the forest based on the active edges
    :param graph: graph whose MD tree needs to be computed
    :param root: the forest which needs to be assembled into a MD tree
    :param vertex_dist: dictionary mapping the vertex with distance from the source
    :param vertex_status: dictionary mapping the vertex to the position w.r.t source

    """
    #print root
    x_used = []
    for v in graph.vertices():
        if v in vertex_status and vertex_status[v]==SOURCE:
            continue
        x = []     #list of vertices connected through active edges to v
        for e in graph.edges_incident(v):
            if vertex_dist[e[0]]!=vertex_dist[e[1]]:
                x.append(e[0] if e[0]!=v else e[1])
        #print "x=",x
        if set(x) not in x_used:
            x_used.append(set(x))
            maximal_subtrees_with_leaves_in_x(root, v, x, vertex_status, False, 0)
    get_child_splits(root)
    #print root

def get_child_splits(root):
    if root[0].node_type!=NORMAL:
        for tree in root[1]:
            get_child_splits(tree)
            root[0].set_node_split(tree[0].node_split)

def maximal_subtrees_with_leaves_in_x(root, v, x, vertex_status, tree_left_of_source, level):
    """
    Refines the forest based on the active edges(x) of vertex v

    :param root: the forest which needs to be assembled into a MD tree
    :param v: the vertex used to refine
    :param x: list of vertices connected to v and at different distance from source compared to v
    :param vertex_status: dictionary mapping the vertex to the position w.r.t source
    :param tree_left_of_source: flag indicating whether tree is
    :param level: indicates the recursion level, 0 for root
    """
    #print "ROOT: ",root
    return_split = NO_SPLIT
    if root[0].node_type == FOREST:
        left_flag = True    #indicates whether tree is left of source, True if left of source
        for tree in root[1]:
            if tree[0].node_type == NORMAL and tree[1][0] in vertex_status and vertex_status[tree[1][0]] == SOURCE:
                left_flag = False
            #print "left_flag ",left_flag, tree
            subtree_result = maximal_subtrees_with_leaves_in_x(tree, v, x, vertex_status, left_flag, level)
            #print subtree_result
            if subtree_result:
                #Mark the ancestors
                root[0].set_node_split(subtree_result[1])
            """if tree[0].node_type == FOREST:
                index = root[1].index(tree)
                root[1].remove(tree)
                for subtree in tree:
                    root[1].insert(index,subtree)
                    index += 1
                    #root[1].append(subtree)"""
    elif root[0].node_type != NORMAL:
        flag = True
        split_flag = False
        for subtree in root[1]:
            #if subtree[0].node_type!=NORMAL and len(subtree[1])==1:
                #continue
            subtree_result = maximal_subtrees_with_leaves_in_x(subtree, v, x, vertex_status, tree_left_of_source, level+1)
            #print subtree_result
            if subtree_result:
                flag = flag and subtree_result[0]
                root[0].set_node_split(subtree_result[1])
                if subtree_result[0]:
                    split_flag = True
        if flag:
            #return if all subtrees are in x, no split required
            return [True, root[0].node_split]
        elif split_flag:    #split required`
            split = LEFT_SPLIT
            #print "ROOT: ", root
            #if v is right of source and tree is also right of source then right split
            if vertex_status[v] == RIGHT_OF_SOURCE and not tree_left_of_source:
                split = RIGHT_SPLIT

            if root[0].node_type == PRIME:
                #mark all the children of prime nodes
                root[0].set_node_split(split)
                for subtree in root[1]:
                    subtree[0].set_node_split(split)
                return [False, split]

            Ta = [] #contains subtrees with leaves in x
            Tb = [] #contains subtrees with leaves not in x
            for subtree in root[1]:
                subtree_result = maximal_subtrees_with_leaves_in_x(subtree, v, x, vertex_status, tree_left_of_source, level+1)
                #print "LEVEL: ",level, subtree_result, subtree
                root[0].set_node_split(subtree_result[1])
                root[0].set_node_split(split)
                if subtree_result[0]:
                    Ta.append(subtree)
                else:
                    Tb.append(subtree)
                node_type = root[0].node_type

            if root[0].is_separated:
                return [flag, root[0].node_split]
            #Add nodes for both Ta and Tb
            root[0].is_separated = True
            root[1] = []
            root[1].append(create_parallel_node())
            root[1][-1][0].node_type = node_type
            root[1][-1][0].node_split = root[0].node_split
            root[1].append(create_parallel_node())
            root[1][-1][0].node_type = node_type
            root[1][-1][0].node_split = root[0].node_split
            root[1][-1][0].comp_num = root[0].comp_num
            #if level==0:
                #root[0].node_type = FOREST
            """    if split == LEFT_SPLIT:
                    root[1][-2][1] = Ta
                    root[1][-1][1] = Tb
                else:
                    root[1][-2][1] = Ta
                    root[1][-1][1] = Tb"""
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

if __name__ == "__main__":
    d = {1: [2],
         2: [1,3,4], 3: [2,5,6],
         4: [2], 5: [6,3],
         6: [3,5]
         }
    g = Graph(d)
    root = []
    root.append([g, modular_decomposition(g)])
    d1 = {1:[5,4,3,24,6,7,8,9,2,10,11,12,13,14,16,17],
        2:[1],
        3:[24,9,1],
        4:[5,24,9,1],
        5:[4,24,9,1],
        6:[7,8,9,1],
        7:[6,8,9,1],
        8:[6,7,9,1],
        9:[6,7,8,5,4,3,1],
        10:[1],
        11:[12,1],
        12:[11,1],
        13:[14,16,17,1],
        14:[13,17,1],
        16:[13,17,1],
        17:[13,14,16,18,1],
        18:[17],
        24:[5,4,3,1]
        }
    g1 = Graph(d1)
    root.append([g1, modular_decomposition(g1)])
    d2 = {
        1:[2,3,4],
        2:[1,4,5,6,7],
        3:[1,4,5,6,7],
        4:[1,2,3,5,6,7],
        5:[2,3,4,6,7],
        6:[2,3,4,5,8,9,10,11],
        7:[2,3,4,5,8,9,10,11],
        8:[6,7,9,10,11],
        9:[6,7,8,10,11],
        10:[6,7,8,9],
        11:[6,7,8,9]
    }
    g2 = Graph(d2)
    root.append([g2, modular_decomposition(g2)])
    g3 = HallJankoGraph()
    root.append([g3, modular_decomposition(g3)])
    g4 = ChvatalGraph()
    root.append([g4, modular_decomposition(g4)])
    g5 = DesarguesGraph()
    root.append([g5, modular_decomposition(g5)])
    g6 = FlowerSnark()
    root.append([g6, modular_decomposition(g6)])
    g7 = FruchtGraph()
    root.append([g7, modular_decomposition(g7)])
    g8 = HeawoodGraph()
    root.append([g8, modular_decomposition(g8)])
    g9 = MoebiusKantorGraph()
    root.append([g9, modular_decomposition(g9)])
    g10 = PappusGraph()
    root.append([g10, modular_decomposition(g10)])
    g11 = PetersenGraph()
    root.append([g11, modular_decomposition(g11)])
    g12 = ThomsenGraph()
    root.append([g12, modular_decomposition(g12)])
    g13 = CycleGraph(17)
    root.append([g13, modular_decomposition(g13)])
    g14 = TetrahedralGraph()
    root.append([g14, modular_decomposition(g14)])
    g15 = DodecahedralGraph()
    root.append([g15, modular_decomposition(g15)])
    g16 = OctahedralGraph()
    root.append([g16, modular_decomposition(g16)])
    g17 = IcosahedralGraph()
    root.append([g17, modular_decomposition(g17)])
    g18 = HexahedralGraph()
    root.append([g18, modular_decomposition(g18)])
    g19 = DorogovtsevGoltsevMendesGraph(5)
    root.append([g19, modular_decomposition(g19)])
    g20 = BalancedTree(3,5)
    root.append([g20, modular_decomposition(g20)])
    g21 = CircularLadderGraph(9)
    root.append([g21, modular_decomposition(g21)])
    g22 = CubeGraph(8)
    root.append([g22, modular_decomposition(g22)])
    for index,pair in enumerate(root):
        #if index!=22:
            #continue
        print pair[0].to_dictionary()
        print_md_tree(pair[1],0)
        print "TEST RESULT: ", test_modular_decomposition(pair[1], pair[0])
