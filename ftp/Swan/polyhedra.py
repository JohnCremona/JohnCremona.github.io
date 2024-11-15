##############################################
#
# Standard polyhedra (as graphs)
#
##############################################

from sage.all import Graph

Tetrahedron = Graph([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
                    name="tetrahedron")

Cube = Graph([(0, 1), (0, 3), (0, 7), (1, 2), (1, 6), (2, 4), (2, 7),
              (3, 5), (3, 6), (4, 5), (4, 6), (5, 7)],
             name="cube")

SquarePyramid = Graph([(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (3, 4)],
                    name = "square pyramid")

HexagonalPrism = Graph([(0, 1), (0, 5), (0, 9), (1, 2), (1, 10),
                        (2, 4), (2, 5), (3, 5), (3, 7), (3, 9),
                        (4, 8), (4, 10), (6, 7), (6, 9), (6, 11),
                        (7, 8), (8, 11), (10, 11)],
                       name = "hexagonal prism")

HexagonalCap = Graph([(1,2),(2,3),(3,4),(4,5),(5,6),(6,1),
              (1,7),(2,7),(3,8),(4,8),(5,9),(6,9),
              (7,8),(8,9),(9,7)],
             name="hexagonal cap")

TruncatedTetrahedron = Graph([(0, 6), (0, 8), (0, 10), (1, 5), (1, 8), (1, 11),
                  (2, 7), (2, 9), (2, 11), (3, 4), (3, 5), (3, 9),
                  (4, 5), (4, 6), (6, 10), (7, 9), (7, 10), (8, 11)],
                 name = "truncated tetrahedron")

TriangularPrism = Graph([(1,2),(2,3),(3,1),(4,5),(5,6),(6,4),(1,4),(2,5),(3,6)],
              name="triangular prism")

Cuboctahedron = Graph([(0, 2), (0, 6), (0, 7), (0, 11),
                       (1, 4), (1, 8), (1, 9), (1, 11),
                       (2, 6), (2, 8), (2, 10),
                       (3, 5), (3, 6), (3, 9), (3, 10),
                       (4, 5), (4, 7), (4, 9),
                       (5, 6), (5, 7), (7, 11), (8, 10), (8, 11),
                       (9, 10)],
                      name = "cuboctahedron")

Octahedron = Graph( [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 3),
                     (1, 4), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)],
                    name = "octahedron")

# Some compund polyhedra encountered:

SlicedCube = Graph([(0, 1), (0, 2), (0, 3), (1, 0), (1, 4), (1, 5), (6, 3), (6, 2), (6, 7),
                    (7, 5), (7, 4), (7, 6), (3, 6), (3, 0), (3, 2), (3, 4), (5, 7), (5, 1),
                    (5, 4), (5, 2), (2, 6), (2, 0), (2, 3), (2, 5), (4, 7), (4, 1), (4, 5), (4, 3)],
                   name = "sliced cube")

# = cube with an inner diagonal face, also two triangular prisms glued along a square face

DoubleHexagonalPrism = Graph([(0, 1), (0, 2), (0, 3), (4, 2), (4, 5), (4, 6), (7, 5), (7, 1), (7, 8),
                              (1, 0), (1, 7), (1, 9), (2, 4), (2, 0), (2, 10), (5, 7), (5, 4), (5, 11),
                              (3, 12), (3, 0), (3, 10), (3, 9), (8, 13), (8, 7), (8, 9), (8, 11),
                              (6, 14), (6, 4), (6, 11), (6, 10), (10, 15), (10, 2), (10, 3), (10, 6),
                              (9, 16), (9, 1), (9, 8), (9, 3), (11, 17), (11, 5), (11, 6), (11, 8),
                              (12, 15), (12, 3), (12, 16), (13, 16), (13, 8), (13, 17), (14, 17),
                              (14, 6), (14, 15), (15, 12), (15, 10), (15, 14), (16, 13), (16, 9),
                              (16, 12), (17, 14), (17, 11), (17, 13)],
                             name = "double hexagonal prism")
# Two hexagonal prisms glued along a hexagon

HalfStar = Graph( [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6), (4, 3), (1, 0), (1, 2), (1, 5),
                   (1, 3), (5, 4), (5, 6), (5, 1), (5, 3), (2, 6), (2, 0), (2, 1), (2, 3),
                   (6, 2), (6, 4), (6, 5), (6, 3), (3, 4), (3, 0), (3, 2), (3, 5), (3, 1), (3, 6)],
                  name = "half star")

# Half a stella octangula, also a square prism with two tetrahedra glued on no-adjacent triangles


Unknown = Graph(name="unknown")

# To add a new type of polyhedron, given one G of the new type:
#
# V = G.vertices()
# E = [tuple(V.index(ei) for ei in e[:2])  for e in G.edges()]
# assert G.is_isomorphic(Graph(E))
# E
#
# now add this code with the list of pairs E as first argument:
# NewPoly = Graph(..., name="new name")
#

all_polys = (Tetrahedron, Cube, Octahedron,
             TriangularPrism, SquarePyramid, HexagonalPrism,
             HexagonalCap, TruncatedTetrahedron, Cuboctahedron,
             SlicedCube, DoubleHexagonalPrism, HalfStar,
             Unknown)

def poly_type(pol):
    for G in all_polys:
        if pol.is_isomorphic(G):
            return G.name()
    return "unknown"

def all_poly_types(pols):
    return [poly_type(pol) for pol in pols]

def poly_types(pols):
    n_unknown = sum(1 for pol in pols if poly_type(pol)=='unknown')
    return dict([(std_pol.name(), sum(1 for pol in pols if pol.is_isomorphic(std_pol)))
                 for std_pol in all_polys] + [('unknown', n_unknown)])
