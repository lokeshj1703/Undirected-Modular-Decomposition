from sage.all import Graph
from queue import Queue
# corner cases
# instead of append u require to add the entry of the dict into the present dict

# remove marks before refinement
# after generating forest, place trees in parent list for FOREST case in maximal
# prime node
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

class NodeInfo:

    def __init__(self, node_type):
        self.node_type = node_type
        self.node_split = NO_SPLIT
        self.index_in_root = -1

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

        return string

    def __repr__(self):
        string = ""
        if self.node_type==SERIES:
            string += "SERIES"
        elif self.node_type==PARALLEL:
            string += "PARALLEL"
        elif self.node_type==PRIME:
            string += "PRIME"
        elif self.node_type == FOREST:
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
        return string

    def __eq__(self, other):
        return self.node_type == other.node_type

def modularDecomposition(graph):
    print graph.vertices()
    if graph._directed:
        return ValueError("Graph must be directed")
    if graph.order() == 1:
        root = create_normal_node(graph.vertices()[0])
        print root
        return root
    if not graph.is_connected():
        components = graph.connected_components()
        root = create_parallel_node()
        for component in components:
            root[1].append(modularDecomposition(graph.subgraph(component)))
        print root
        return root
    elif graph.complement().is_connected():
        root = create_prime_node()
    else:
        root = create_series_node()
    print graph.vertices()[0]
    bfs_generator = graph.breadth_first_search(graph.vertices()[0], report_distance=True)
    prev_level_distance = -1
    prev_level_list = []
    vertex_dist = {}
    vertex_status = {}
    vertex_status[graph.vertices()[0]] = SOURCE
    for (vertex, distance) in bfs_generator:
        vertex_dist[vertex] = distance
        print "vertex_dist", vertex, vertex_dist[vertex]
        if distance != prev_level_distance:
            if prev_level_list:
                print "recursive call",prev_level_list
                root[1].append(modularDecomposition(graph.subgraph(prev_level_list)))
            if prev_level_distance==1 and distance!=1:
                for v in prev_level_list:
                    vertex_status[v] = LEFT_OF_SOURCE
            elif prev_level_distance!=0:
                for v in prev_level_list:
                    vertex_status[v] = RIGHT_OF_SOURCE
            prev_level_list = []
            prev_level_distance = distance
        prev_level_list.append(vertex)
    if distance == 1:
        for v in prev_level_list:
            vertex_status[v] = LEFT_OF_SOURCE
    elif distance != 0:
        for v in prev_level_list:
            vertex_status[v] = RIGHT_OF_SOURCE
    print "recursive call", prev_level_list
    root[1].append(modularDecomposition(graph.subgraph(prev_level_list)))
    temp = root[1][1]
    root[1][1] = root[1][0]
    root[1][0] = temp
    root[0].node_type = FOREST
    print root
    print "************REFINEMENT************"
    print "vertex_status: ", vertex_status
    clear_node_split_info(root)
    refine(graph, root, vertex_dist, vertex_status)
    print "************PROMOTE LEFT**********"
    promote_left(root)
    print "************PROMOTE RIGHT************"
    promote_right(root)
    print "************PROMOTE CHILD************"
    promote_child(root)
    assembly(graph, root, vertex_status)
    print root
    return root

def assembly(graph, root, vertex_status):
    print "***********ASSEMBLY**************"
    mu = {}
    source_index = -1
    vertices_in_component = {}
    is_right_connected = {}
    component_index = {}
    component_at_index = {}
    index = 0
    for component in root[1]:
        #component_index[component] = index
        component_at_index[index] = component
        if component[0].node_type==NORMAL and vertex_status[component[1][0]]==SOURCE:
            source_index = root[1].index(component)
        vertices_in_component[index] = get_vertices(component)
        root[1][index][0].index_in_root = index
        index += 1
    index = 0
    for component in root[1]:
        if index < source_index:
            mu[index] = compute_mu_for_co_component(graph, index, source_index, root, vertices_in_component)
        elif index > source_index:
            mu[index] = compute_mu_for_component(graph, index, source_index, root, vertices_in_component)
            is_right_connected[index] = False if get_right_connected(graph, index, index,
                                                                     root, vertices_in_component)\
                                                 ==root[1][-1] \
                                              else True
        index += 1
    mu[source_index] = root[1][source_index]
    print mu
    print vertices_in_component
    print is_right_connected
    print component_index
    print component_at_index
    left = root[1][source_index]
    right = root[1][source_index]
    while not len(root[1])==1:
        print "ROOT: ",root
        [result, source_index] = check_series(root, left, right, source_index, mu)
        if result:
            left = root[1][source_index][1][0]
            continue
        [result, source_index] = check_parallel(root, left, right, source_index, mu, is_right_connected)
        if result:
            right = root[1][source_index][1][-1]
            continue
        [result, source_index] = check_prime(root, left, right, source_index, mu)
        if result:
            if root[1][source_index][1][0][0].index_in_root != -1:
                left = root[1][source_index][1][0]
            if root[1][source_index][1][-1][0].index_in_root != -1:
                right = root[1][source_index][1][-1]

def check_prime(root, left, right, source_index, mu):
    new_right_index = source_index+1 if source_index+1 < len(root[1]) else source_index
    new_left_index = source_index-1 if source_index-1 >=0 else source_index
    right_index_for_mu = new_right_index
    left_index_for_mu = new_left_index
    if left_index_for_mu != source_index:
        while new_right_index<len(root[1])-1 and root[1][new_right_index][0].index_in_root < mu[left_index_for_mu][0].index_in_root:
            new_right_index += 1
    if right_index_for_mu != source_index:
        while new_left_index>0 and root[1][new_left_index][0].index_in_root > mu[right_index_for_mu][0].index_in_root:
            new_left_index -= 1
    temp = new_left_index
    node = create_prime_node()
    while temp <= new_right_index:
        node[1].append(root[1][temp])
        temp += 1
    print "PRIME Indices", new_left_index, new_right_index
    root[1][new_left_index:new_right_index + 1] = []
    root[1].insert(new_left_index, node)
    return [True, new_left_index]

def check_parallel(root, left, right, source_index, mu, is_right_connected):
    new_right_index = source_index
    while new_right_index < len(root[1])-1:
        if mu[root[1][new_right_index+1][0].index_in_root] == mu[left[0].index_in_root]:
            if is_right_connected[root[1][new_right_index+1][0].index_in_root]:
                break
            new_right_index += 1
        else:
            break
    if source_index != new_right_index:
        node = create_parallel_node()
        temp = source_index
        while temp <= new_right_index:
            node[1].append(root[1][temp])
            temp += 1
        root[1][source_index:new_right_index+1] = []
        root[1].insert(source_index, node)
        return [True, source_index]
    return [False, source_index]

def check_series(root, left, right, source_index, mu):
    new_left_index = source_index
    while new_left_index > 0:
        if mu[root[1][new_left_index-1][0].index_in_root] == mu[right[0].index_in_root]:
            new_left_index -= 1
        else:
            break
    if source_index != new_left_index:
        node = create_series_node()
        temp = new_left_index
        while source_index >= temp:
            node[1].append(root[1][temp])
            temp += 1
        root[1][new_left_index:source_index+1] = []
        root[1].insert(new_left_index, node)
        return [True, new_left_index]
    return [False, new_left_index]

def compute_mu_for_co_component(graph, component_index, source_index, root, vertices_in_component):
    index = len(root[1])-1
    mu_for_co_component = root[1][source_index]
    while index > source_index:
        if is_component_connected(graph, component_index, index, vertices_in_component):
            mu_for_co_component = root[1][index]
            return mu_for_co_component
        index -= 1
    return mu_for_co_component

def get_right_connected(graph, component_index, source_index, root, vertices_in_component):
    index = source_index + 1
    while index < len(root[1]):
        if is_component_connected(graph, component_index, index, vertices_in_component):
            return root[1][index-1]
        index += 1
    return root[1][index-1]

def compute_mu_for_component(graph, component_index, source_index, root, vertices_in_component):
    index = 0
    mu_for_component = root[1][0]
    while index < source_index:
        if is_component_connected(graph, component_index, index, vertices_in_component):
             mu_for_component = root[1][index+1]
        index += 1
    return mu_for_component

def is_component_connected(graph, index1, index2, vertices_in_component):
    vertices = vertices_in_component[index1]
    index2_vertices_set = set(vertices_in_component[index2])
    for vertex in vertices:
        neighbors = graph.neighbors(vertex)
        if not index2_vertices_set.isdisjoint(set(neighbors)):
            return True
    return False

def get_vertices(component):
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
    q = Queue()
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        print "parent=",parent
        print "child =",child
        if child[0].node_type==NORMAL:
            continue
        to_remove = []
        index = parent[1].index(child)
        for tree in child[1]:
            print tree[0].has_left_split(), child[0].has_left_split()
            if tree[0].has_left_split() and child[0].has_left_split():
                parent[1].insert(index, tree)
                index -= 1
                to_remove.append(tree)
                q.put([parent, tree])
            else:
                q.put([child, tree])
        for tree in to_remove:
            child[1].remove(tree)

def promote_right(root):
    q = Queue()
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        print "parent=",parent
        print "child =",child
        if child[0].node_type==NORMAL:
            continue
        to_remove = []
        index = parent[1].index(child)
        for tree in child[1]:
            if tree[0].has_right_split() and child[0].has_right_split():
                parent[1].insert(index+1, tree)
                index += 1
                to_remove.append(tree)
                q.put([parent, tree])
            else:
                q.put([child, tree])
        for tree in to_remove:
                child[1].remove(tree)

def promote_child(root):
    q = Queue()
    for tree in root[1]:
        q.put([root, tree])
    while not q.empty():
        [parent, child] = q.get()
        print "parent=",parent
        print "child =",child
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

def clear_node_split_info(root):
    root[0].node_split = NO_SPLIT
    if root[0].node_type!=NORMAL:
        for subroot in root[1]:
            clear_node_split_info(subroot)

def refine(graph, root, vertex_dist, vertex_status):
    for v in graph.vertices():
        if v in vertex_status and vertex_status[v]==SOURCE:
            continue
        x = []
        for e in graph.edges_incident(v):
            if vertex_dist[e[0]]!=vertex_dist[e[1]]:
                x.append(e[0] if e[0]!=v else e[1])
        print "x=",x
        maximal_subtrees_with_leaves_in_x(root, v, x, vertex_status, False, 0)

def maximal_subtrees_with_leaves_in_x(root, v, x, vertex_status, tree_left_of_source, level):
    print root
    return_split = NO_SPLIT
    if root[0].node_type == FOREST:
        left_flag = True
        for tree in root[1]:
            if tree[0].node_type == NORMAL and tree[1][0] in vertex_status and vertex_status[tree[1][0]] == SOURCE:
                left_flag = False
            print "left_flag ",left_flag, tree
            subtree_result = maximal_subtrees_with_leaves_in_x(tree, v, x, vertex_status, left_flag, level)
            print subtree_result
            if subtree_result:
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
            subtree_result = maximal_subtrees_with_leaves_in_x(subtree, v, x, vertex_status, tree_left_of_source, level+1)
            print subtree_result
            if subtree_result:
                flag = flag and subtree_result[0]
                if subtree_result[0]:
                    split_flag = True
        if flag:
            return [True, return_split]
        elif split_flag:
            split = LEFT_SPLIT
            if vertex_status[v] == RIGHT_OF_SOURCE and not tree_left_of_source:
                split = RIGHT_SPLIT

            if root[0].node_type == PRIME:
                root[0].set_node_split(split)
                for subtree in root[1]:
                    subtree[0].set_node_split(split)
                return [True, split]

            Ta = []
            Tb = []
            for subtree in root[1]:
                subtree_result = maximal_subtrees_with_leaves_in_x(subtree, v, x, vertex_status, tree_left_of_source, level+1)
                print subtree_result
                root[0].set_node_split(subtree_result[1])
                root[0].set_node_split(split)
                if subtree_result[0]:
                    Ta.append(subtree)
                else:
                    Tb.append(subtree)
                root[1] = []
                node_type = root[0].node_type

            return_split = root[0].node_split
            root[1].append(create_parallel_node())
            root[1][-1][0].node_type = node_type
            root[1][-1][0].node_split = root[0].node_split
            root[1].append(create_parallel_node())
            root[1][-1][0].node_type = node_type
            root[1][-1][0].node_split = root[0].node_split
            if split == LEFT_SPLIT:
                root[1][-2][1] = Ta
                root[1][-1][1] = Tb
            else:
                root[1][-2][1] = Tb
                root[1][-1][1] = Ta
            if level==0:
                root[0].node_type = FOREST

        return [flag, return_split]
    elif root[1][0] in x:
        return [True, return_split]
    else:
        return [False, return_split]

def create_prime_node():
    return [NodeInfo(PRIME), []]

def create_parallel_node():
    return [NodeInfo(PARALLEL), []]

def create_series_node():
    return [NodeInfo(SERIES), []]

def create_normal_node(vertex):
    return [NodeInfo(NORMAL), [vertex]]

if __name__ == "__main__":
    d = {1: [2],
         2: [1,3,4], 3: [2,5,6],
         4: [2], 5: [6,3],
         6: [3,5]
         }
    g = Graph(d)
    print modularDecomposition(g)
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
    print modularDecomposition(g1)