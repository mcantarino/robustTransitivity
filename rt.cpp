/* rt.cpp
 *
 * Verify that a certain diffeomorphism of the 3-torus is robustly transitive.
 *
 * This is the main source file for the computer code accompanying
 *
 * Marisa Cantarino, Andy Hammerlindl, Warwick Tucker
 * "A computer-assisted proof of robust transitivity."
 */

// Includes {{{1

#include <string>
#include <vector>
#include <iostream>
#include <cassert>

#include "capd/capdlib.h"
#include "tarjan.h"
#include "svd.h"


// Helper functions {{{1

// Macros to print out values for debugging.
#ifndef SAY
#define SAY(x) \
    std::cerr << #x << std::endl;
#endif
#ifndef TEST
#define TEST(x) \
    std::cerr << #x << " = " << (x) << std::endl;
#endif

const int DIM = 3;

#ifndef FORDIM
#define FORDIM(k) \
    for (int k=0; k<DIM; ++k)
#endif

// Shorter type names for common interval objects.
using Ival = capd::DInterval;
using Vec = capd::vectalg::Vector<Ival,DIM>;
using Mat = capd::vectalg::Matrix<Ival,DIM,DIM>;

using capd::abs;

using std::cout, std::cerr, std::endl, std::string, std::ostream;

// Note that we always write out std::vector to avoid confusion with
// actual vectors.

float Inf(Ival x) { return leftBound(x); }
float Sup(Ival x) { return rightBound(x); }

Ival midpoint(Ival x) { return x.mid(); }

bool intersects(Ival x, Ival y) {
    Ival ignore;
    return intersection(x, y, ignore);
}

bool intersects(Vec u, Vec v) {
    Vec ignore;
    return intersection(u, v, ignore);
}

bool disjoint(Ival x, Ival y) { return not intersects(x, y); }
bool disjoint(Vec u, Vec v) { return not intersects(u, v); }

const Ival PI = Ival::pi();
Ival sinpi(Ival x) { return sin(PI * x); }
Ival cospi(Ival x) { return cos(PI * x); }

Ival norm(Vec v) { return euclNorm(v); }

Mat cramerInverseMatrix(Mat A) {
    // Compute minors with signs and transposing.
    Ival m00 = A[1][1] * A[2][2] - A[2][1] * A[1][2];
    Ival m01 = A[0][2] * A[2][1] - A[0][1] * A[2][2];
    Ival m02 = A[0][1] * A[1][2] - A[0][2] * A[1][1];
    Ival m10 = A[1][2] * A[2][0] - A[1][0] * A[2][2];
    Ival m11 = A[0][0] * A[2][2] - A[0][2] * A[2][0];
    Ival m12 = A[1][0] * A[0][2] - A[0][0] * A[1][2];
    Ival m20 = A[1][0] * A[2][1] - A[2][0] * A[1][1];
    Ival m21 = A[2][0] * A[0][1] - A[0][0] * A[2][1];
    Ival m22 = A[0][0] * A[1][1] - A[1][0] * A[0][1];

    // Compute the 3 by 3 determinant.
    Ival det = A[0][0] * m00 + A[0][1] * m10 + A[0][2] * m20;

    Ival invdet = Ival(1.0) / det;

    Mat out;
    out[0][0] = m00 * invdet;
    out[0][1] = m01 * invdet;
    out[0][2] = m02 * invdet;
    out[1][0] = m10 * invdet;
    out[1][1] = m11 * invdet;
    out[1][2] = m12 * invdet;
    out[2][0] = m20 * invdet;
    out[2][1] = m21 * invdet;
    out[2][2] = m22 * invdet;

    return out;
}

inline
Mat inverseMatrix(Mat A) {
    return cramerInverseMatrix(A);
}

// MATLAB-style function for an identity matrix.
inline
Mat eye(int n) {
    assert(n == DIM);
    Mat I;
    FORDIM(k)
        I[k][k] = Ival(1.0);
    return I;
}


// Build a diagonal matrix from entries of a vector.
inline
Mat diag(Vec v) {
    Mat D;
    FORDIM(i)
        D[i][i] = v[i];
    return D;
}

inline
Ival det(Mat A) {
    // Compute minors with signs and transposing.
    Ival m00 = A[1][1] * A[2][2] - A[2][1] * A[1][2];
    Ival m10 = A[1][2] * A[2][0] - A[1][0] * A[2][2];
    Ival m20 = A[1][0] * A[2][1] - A[2][0] * A[1][1];

    // Compute the 3 by 3 determinant.
    Ival out = A[0][0] * m00 + A[0][1] * m10 + A[0][2] * m20;
    return out;
}

// Are all symmetric matrices enclosed in A positive definite?
inline
bool posdef(Mat A) {
    // A small speed-up would be to reuse the det2 minor in the
    // determinant calculation.
    Ival det1 = A[0][0];
    Ival det2 = A[0][0] * A[1][1] - A[1][0] * A[0][1];
    Ival det3 = det(A);
   
    Ival zero(0.0);
    return det1 > zero and det2 > zero and det3 > zero;
}


// Throughout this code, R is defined as the cube [-1,1]^3.
Vec R(Ival(-1,1), Ival(-1,1), Ival(-1,1));

Vec origin(0.0, 0.0, 0.0);

/* Cut an interval into roughly equal length subintervals.
 *
 * We use "partition" instead of "split" in the function name
 * to try to avoid confusion with the partially hyperbolic splitting.
 */
std::vector<Ival> partitionInterval(Ival J, int n)
{
    double lo = Inf(J), hi = Sup(J);
    double w = (hi-lo)/n;

    std::vector<Ival> acc;
    double left = lo;
    for (int i = 1; i < n; ++i) {
        double right = lo + i * w;
        acc.push_back(Ival(left, right));
        left = right;
    }

    acc.push_back(Ival(left, hi));
    assert((int)acc.size() == n);

    return acc;
}


// Test for intersection modulo the integers.
inline
bool modIntersects(Ival I, Ival J)
{
    Ival K = J-I;

    // Round inward to the nearest integer.
    double m = std::ceil(Inf(K));
    double n = std::floor(Sup(K));

    return m <= n;
}


// Determines if two boxes intersect on the torus.
inline
bool modIntersects(Vec u, Vec v)
{
    FORDIM(k)
        if (not modIntersects(u[k], v[k]))
            return false;
    return true;
}


/* Return the unique integer n such that I+n intersects J.
 *
 * This returns the result as a zero-width interval.
 *
 * This fails an assert if n does not exist or is not unique.
 */
Ival shiftInterval(Ival I, Ival J)
{
    /* Here x+n = y if and only if n = y-x, so consider K = J-I.
     *
     * This is implemented by finding all integers in
     * K = J-I and determining if there is exactly one such integer.
     * The calculation of the endpoints rounds outward,
     * so in some rare cases, it may include an integer not
     * in the mathematically correct difference J-I.
     *
     * In practice, this function is only used when
     * width(I) + width(J) is not close to 1.
     */
    Ival K = J-I;
    
    // Round inward to the nearest integer.
    double m = std::ceil(Inf(K));
    double n = std::floor(Sup(K));

    assert(m == n);
    return n;
}


// Return the unique integer-valued vector z such that u+z intersects v.
Vec shiftVector(Vec u, Vec v)
{
    return Vec(
            shiftInterval(u[0], v[0]),
            shiftInterval(u[1], v[1]),
            shiftInterval(u[2], v[2]));
}


// Returns all integers contained in the interval.
std::vector<Ival> intInInterval(Ival K)
{
    double m = std::ceil(Inf(K));
    double n = std::floor(Sup(K));

    // For the intervals used in the overall code,
    // the following floating-point addition by 1.0 will be exact.
    std::vector<Ival> nz;
    for (double x = m; x <= n; x = x + 1.0) {
        assert(K.contains(x));
        nz.push_back(x);
    }

    if (nz.size() > 0) {
        assert(not K.contains(nz.front() - 1.0));
        assert(not K.contains(nz.back() + 1.0));
    }

    return nz;
}


// Returns all integers n such that J+n intersects K.
std::vector<Ival> allShiftIntervals(Ival J, Ival K)
{
    return intInInterval(K-J);
}


// Return all lattice translations such that u+z intersects v.
std::vector<Vec> allShiftVectors(Vec u, Vec v)
{
    std::vector<Vec> acc;
    for (Ival nx : allShiftIntervals(u[0], v[0]))
    for (Ival ny : allShiftIntervals(u[1], v[1]))
    for (Ival nz : allShiftIntervals(u[2], v[2]))
        acc.push_back(Vec(nx,ny,nz));
    return acc;
}


// AffineMap {{{1

// Data structure to represent a map of the form
// R^3 -> R^3, v mapsto A*v + p;
class AffineMap {
public:
    Mat A;
    Mat Ainv;
    Vec p;

    AffineMap(Mat A, Vec p) : A(A), Ainv(cramerInverseMatrix(A)), p(p) {}

    Mat deriv() { return A; }
    Mat inverseDeriv() { return Ainv; }

    Vec eval(Vec v) { return A*v + p; }
    Vec operator()(Vec v) { return eval(v); }

    // Evaluate the inverse of this map on a set
    Vec inverseEval(Vec v) { return inverseDeriv()*(v-p); }

    AffineMap composeWith(AffineMap& g) {
        return AffineMap(A*g.A, A*g.p + p);
    }
};

std::ostream& operator<<(std::ostream& os, AffineMap f) {
    return os << "AffineMap A: " << f.A << " p: " << f.p;
}

AffineMap translation(Vec p) {
    return AffineMap(eye(3), p);
}

AffineMap affineId() {
    return translation(origin);
}

// Affine map taking [-1,1]^3 to B.
AffineMap zoomMap(Vec B) {
    Mat A;
    Vec p;

    for (int i = 0; i < 3; ++i) {
        p[i] = midpoint(B[i]);
        A[i][i] = right(B[i]) - p[i];
    }

    return AffineMap(A, p);
}


/* For a vector u = (1, u_y, u_z), produce a matrix corresponding to
 *
 *     (x,y,z) -> (x, y + x u_y, z + x u_z).
 *
 */
Mat shearMatrix(Vec u)
{
    assert(u[0] == 1.0);
    Mat A = eye(3);
    A.column(0) = u;
    return A;
}

AffineMap shearMap(Vec u, Vec p) {
    return AffineMap(shearMatrix(u), p);
}


// Settings {{{1

// Settings that depend on if we are analysing f or its inverse.
class DirectedSettings {
public:
    // To verify the weak partially hyperbolic splitting,
    // we divide the fundamental domain [0,1]^3 into split^3 smaller cubes.
    int split;

    // The slope of the 1-dimensional unstable cone in each smaller cube.
    double slope;

    // The scale of the sides of the dynamical boxes that
    // cover the smaller cubes.
    double scale;

    // The huge box centered at the fixed point has scales
    // (0.01, hugeScale, hugeScale)
    // in order to make weakly covering this box as easy as possible.
    double hugeScale;
};


class Settings {
public:
    // The parameters b and k which define the diffeomorphism on the 3-torus.
    Ival b;
    int k;

    // The region V = Vx times Vy times Vz containing the blender. 
    // Note that the code in many places assumes that Vy is equal to the
    // interval [0,1].
    Vec V;

    // When verifying that the invariant set inside V is a transitive
    // horseshoe, horseSplit is how many boxes to split V along the x and z
    // directions.
    // The split in the y direction is chosen to make boxes roughly cubic.
    int horseSplit;

    // Scale of the dynamical boxes in the horseshoe.
    double horseScale;

    // How finely to split the blender into bunches.
    // This gives the split in the x and z directions.
    // The split in the y direction is chosen to
    // make rectangles roughly square.
    int bunchSplit;

    // The slope of the (slanted) cones in the blender.
    double bunchSlope;

    // Settings for the weak partially hyperbolic splittings.
    // These are different for the forward and backward dynamics.
    DirectedSettings back;
    DirectedSettings forth;
};


/* Enclose the image under F of a box. */
Vec forwardImage(Settings& F, Vec box) {
    /* The map takes x,y,z to
     *
     *     k * x - y - z
     *     x + y - b * sin(2 * pi * x)
     *     x
     *
     */

    Ival x = box[0], y = box[1], z = box[2];
    Ival s = F.b * sinpi(2.0 * x);

    Vec out = {
        F.k*x - y - z,
        x + y - s,
        x
    };

    return out;
}

/* Enclose the derivative in a box. */
Mat forwardDeriv(Settings& F, Vec box) {

    /* The Jacobian is
     *
     *     k   -1 -1
     *     1+c  1  0
     *     1    0  0
     *
     *  where c = -2 * pi * b * cos(2 * pi * x)
     *
     */

    Ival x = box[0];
    Ival c = (-2.0) * PI * F.b * cospi(2.0 * x);

    Mat out;

    out[0][0] = Ival(F.k);     out[0][1] = Ival(-1.0); out[0][2] = Ival(-1.0);
    out[1][0] = Ival(1.0) + c; out[1][1] = Ival(1.0);
    out[2][0] = Ival(1.0);

    return out;
}

/* Enclose the image under f inverse of a box. */
Vec backwardImage(Settings& F, Vec box) {
    
    /* The inverse map takes x,y,z to
     *
     *     z
     *     y - z + b * sin(2 * pi * z)
     *     -x -y - b * sin(2 * pi * z) + (k+1) * z
     *
     */

    Ival x = box[0], y = box[1], z = box[2];
    Ival s = F.b * sinpi(2.0 * z);

    Vec out = {
        z,
        y - z + s,
        -(x + y + s) + (F.k+1) * z};

    return out;
}

/* Enclose the deriv of f inverse for a box. */
Mat backwardDeriv(Settings& F, Vec box) {

    /*  The Jacobian is
     *     0  0    1
     *     0  1   -1 + 2 pi b cos(2 pi z)
     *    -1 -1  k+1 - 2 pi b cos(2 pi z)
     *
     */

    Ival z = box[2];
    Ival c = 2 * PI * F.b * cospi(2.0 * z);

    Mat out;
                                                    out[0][2] = Ival(1.0);
                            out[1][1] =  Ival(1.0); out[1][2] = Ival(-1.0) + c;
    out[2][0] = Ival(-1.0); out[2][1] = Ival(-1.0); out[2][2] = Ival(F.k+1) - c;

    return out;
}


// Dynamics {{{1

// Datatype to specify if we are mapping forward by f
// or backwards by f inverse.
enum BackOrForth { BACK = 0,  FORTH };

std::ostream& operator<<(std::ostream& os, BackOrForth way) {
    return os << (way==BACK ? "BACK" : "FORTH");
}

/* A thin wrapper around the Settings class.
 * This also includes a field to say if we are considering f or its inverse.
 * The class is callable, so f(u) gives an enclosure of
 * the image of f (or its inverse) on the box u.
 */
class Dyn {
public:
    Settings& settings;
    BackOrForth way;

    Dyn(Settings& s, BackOrForth way) : settings(s), way(way) {}

    DirectedSettings& directedSettings() {
        return way==FORTH ? settings.forth : settings.back;
    }
    
    Vec operator()(Vec B) {
        return way==FORTH ? forwardImage(settings, B) :
                            backwardImage(settings, B);
    }

    Vec operator()(Ival x, Ival y, Ival z) {
        return this->operator()(Vec(x,y,z));
    }

    Mat deriv(Vec B) {
        return way==FORTH ? forwardDeriv(settings, B) :
                            backwardDeriv(settings, B);
    }

    Dyn inverse() {
        return Dyn(settings, way==FORTH ? BACK : FORTH);
    }

    // Shortcuts for commonly accessed settings.
    Vec  V()  { return settings.V; }
    Ival Vx() { return settings.V[0]; }
    Ival Vy() { return settings.V[1]; }
    Ival Vz() { return settings.V[2]; }
};


// Splittings {{{1

// Convert matrix to non-rigorous floating point values.
linalg::Mat toLinAlg(Mat A) {
    linalg::Mat out;
    FORDIM(i) FORDIM(j)
        out[i][j] = Inf(A[i][j]);
    return out;
}

// Fill a column with zero-width intervals.
void columnFromLinAlg(Mat& A, int col, linalg::Vec v) {
    FORDIM(i)
        A[i][col] = Ival(v[i]);
}

/** Approximate the partially hyperbolic splitting at the midpoint of the box.
 *
 *  The returned matrix is [ v^u | v^c | v^s ]
 *  where each column is a unit vector
 *  approximating the unstable, center, and stable directions.
 */
Mat splitting(Dyn f, Vec B)
{
    Settings& s = f.settings;
    Vec p0 = midVector(B);
    Vec p1 = forwardImage(s, p0);
    Vec pm = backwardImage(s, p0);

    linalg::Mat Dh = toLinAlg(forwardDeriv(s, p0));
    linalg::Mat Dh2 = toLinAlg(forwardDeriv(s, p1));
    linalg::Mat Dhi = toLinAlg(backwardDeriv(s, p0));
    linalg::Mat Dhi2 = toLinAlg(backwardDeriv(s, pm));

    linalg::Mat V  = singularVectors(Dh2 * Dh);
    linalg::Mat Vi = singularVectors(Dhi2 * Dhi);

    // v^s is approximated by the vector most contracted by Df^2.
    linalg::Vec vs = V.col(2);

    // v^u is approximated by the vector most contracted by Df^{-2}. 
    linalg::Vec vu = Vi.col(2);

    // Intersect the cu and cs plane approximations using the cross product
    // of their normal vectors.
    linalg::Vec vc = linalg::normalise(linalg::cross(V.col(0), Vi.col(0)));

    // For consistency and to help debugging,
    // we negate entries if necessary to make
    // the diagonal have positive entries.
    if (vu[0] < 0.0)
        vu = -vu;
    if (vc[1] < 0.0)
        vc = -vc;
    if (vs[2] < 0.0)
        vs = -vs;

    // Fill in the matrix as [vu | vc | vs] if going forward, and
    // [vs | vc | vu] if going backward.
    Mat A;
    if (f.way == FORTH) {
        columnFromLinAlg(A, 0, vu);
        columnFromLinAlg(A, 1, vc);
        columnFromLinAlg(A, 2, vs);
    } else { /* f.way == BACK */
        columnFromLinAlg(A, 0, vs);
        columnFromLinAlg(A, 1, vc);
        columnFromLinAlg(A, 2, vu);
    }

    return A;
}


// Local map {{{1

/* A representation of the local map between two dynamical boxes.
 * 
 * This stores the pieces of the composition
 *
 *     v -> A2 inv( f(A1(v)) + z )
 *
 * where A1 and A2 are affine maps, f is a non-linear function, and
 * z is a lattice point in Z^3.
 */
class LocalMap {
public:
    AffineMap A2;
    Dyn f;
    Vec z;
    AffineMap A1;

    LocalMap(AffineMap A2, Dyn f, Vec z, AffineMap A1)
        : A2(A2), f(f), z(z), A1(A1) {}

    // Enclose the derivative on a box B.
    Mat deriv(Vec B) {
        return A2.inverseDeriv() * f.deriv(A1.eval(B)) * A1.deriv();
    }

    // Simple eval using enclosures.
    Vec simpleEval(Vec p) {
        return A2.inverseEval(f(A1.eval(p))+z);
    }

    // Evaluate using the midpoint and derivatives.
    Vec eval(Vec B) {
        Vec p = midVector(B);
        Vec q = simpleEval(p);
        return q + deriv(B)*(B-p);
    }

    // Convenience functions using () for eval.
    Vec operator()(Vec B) { return eval(B); }
    Vec operator()(Ival x, Ival y, Ival z) {
        return eval(Vec(x,y,z));
    }
};


// Cones {{{1

/* A cone generated by a rectangle.
 *
 * This is a thin wrapper around a rectangle of the form
 * rect = (1, y, z) where y and z are intervals and the cone
 * is generated by all real scalings of vectors in rect.
 */
class Cone {
public:
    Vec rect;

    Cone(Vec rect) : rect(rect) { assert(rect[0] == 1.0); }
    Cone(Ival y, Ival z) : rect(Ival(1.0), y, z) {}

    Ival y() { return rect[1]; }
    Ival z() { return rect[2]; }

    // Test if this cone lies in the interior of another.
    bool inside(Cone other) {
        return y().subsetInterior(other.y()) and
               z().subsetInterior(other.z());
    }
    
    // Increase a cone slightly, so that the original cone is
    // in the interior of the returned cone.
    Cone pad() {
        Ival fuzz = 1e-9*Ival(-1,1);
        return Cone(y()+fuzz, z()+fuzz);
    }
};

// The standard slope = 1 cone.
Cone standardCone(Ival(-1,1), Ival(-1,1));

std::ostream& operator<<(std::ostream& os, Cone c) {
    return os << "Cone(" << c.rect[1] <<", " << c.rect[2] << ")";
}

// Enclose a linear map applied to a cone.
Cone operator*(Mat A, Cone cone) {
    auto u = A*cone.rect;
    assert(not u[0].contains(Ival(0)));
    return Cone(u[1]/u[0], u[2]/u[0]);
}


// Cone boxes {{{1

/* A cone box is the image of an axis-aligned box B
 * under an affine map A along with a constant cone
 * family defined on B = B_x times B_y times B_z.
 *
 * Mathematically speaking, a curve in this cone box is a
 * the composition with A of a curve of the form gamma : B_x -> B where
 * gamma(t) = (t, gamma_y(t), gamma_z(t)) is the graph of a function
 * from B_x to B_y times B_z and the tangent vectors
 * gamma'(t) lie in the cone family for all t.
 *
 * When building a cone box, we can compose the affine map A
 * with an affine ``zoom'' map that takes [-1,1]^3 to B
 * and assume WLOG that B is equal to [-1,1]^3.
 * Therefore, we do not store a box B in the actual class.
 * All cone boxes, once constructed, are assumed to be defined on [-1,1]^3.
 *
 */
class ConeBox {
public:
    AffineMap A;
    Cone cone;

    ConeBox(AffineMap A, Cone cone) : A(A), cone(cone) {}

    // The location of the center of the box.
    Vec center() { return A.p; }

    // How far the image extends in each direction.
    Vec sizes() {
        Mat D = A.deriv();
        return Vec(norm(D.column(0)), norm(D.column(1)), norm(D.column(2)));
    }

    // Return an axis-aligned box enclosing the cone box.
    Vec enclosure() { return A(R); }

};


using ConeBoxes = std::vector<ConeBox>;


std::ostream& operator<<(std::ostream& out, ConeBox box) {
    return out << "ConeBox: " << box.A << endl << box.cone;
}


// Build a cone box, rescaled to use [-1,1]^3 as the domain.
ConeBox buildConeBox(AffineMap A, Vec B, Cone cone)
{
    /* The deriv of the zoom map takes a vector
     * (1, vy, vz) to (axx, ayy*vy, azz*vz) which rescales to
     * (1, ayy*vy/axx, azz*vz/axx).
     * This lies in the original cone (1, cy, cz) if and only if
     * (1, vy, vz) lies in (1, axx*cy/ayy, axx*cz/azz).
     */

    AffineMap Z = zoomMap(B);
    Cone zcone = Z.inverseDeriv() * cone;
    return ConeBox(A.composeWith(Z), zcone);
}

/* Use the splitting to construct a cone box at a point.
 *
 * The cone box is centered at p, and the axes in local coordinates
 * are mapped to the directions of the partially hyperbolic splitting
 * and scaled by the factors given in scales.
 */
ConeBox dynamicalConeBox(Dyn f, Vec p, Vec scales, Cone cone)
{
    assert(scales[0] > 0);
    assert(scales[1] > 0);
    assert(scales[2] > 0);

    AffineMap A(splitting(f, p)*diag(scales), p);
    return ConeBox(A, cone);
}

// Verify that Df maps cones into cones.
bool coneInclusion(Dyn f, ConeBox source, ConeBox target)
{
    /* Since we are just looking the derivative,
     * we can construct a local map using any lattice translation.
     */
    LocalMap floc(target.A, f, origin, source.A);

    /* We consider any point in the source box, even if its image is not
     * necessarily in the target box.
     */
    return (floc.deriv(R)*source.cone).inside(target.cone);
}


// Compose f with the affine map of the coneBox.
LocalMap halfLocalMap(Dyn f, ConeBox box)
{
    return LocalMap(affineId(), f, origin, box.A);
}


// Seed boxes {{{1

/* A cone box with an axis-aligned ``seed''.
 *
 * Here, the seed is in the manifold, that is, in R^3, the universal cover of
 * the 3-torus and not in the local coordinates of the cone box.
 * The cone box should be large enough that it contains the seed.
 */
class SeedBox {
public:
    ConeBox coneBox;
    Vec seed;

    SeedBox(ConeBox coneBox, Vec seed)
        : coneBox(coneBox), seed(seed) {}

    SeedBox(AffineMap A, Cone cone, Vec seed)
        : coneBox(A, cone), seed(seed) {}

    ConeBox& asConeBox() { return coneBox; }

    // Enclose the seed in the local coordinates of the cone box.
    Vec localSeed() { return coneBox.A.inverseEval(seed); }

    // Test if the seed is inside the dynamical box.
    bool seedIsInside() { return subset(localSeed(), R); }

    // Test if every curve which both intersects the seed and stays tangent to
    // the cone exits the left and right faces of the cube.
    bool curvesAreGood()
    {
        Ival I(-1,1);
        Vec s = localSeed();
        Ival sx = s[0], sy = s[1], sz = s[2];
        Ival vy = coneBox.cone.y(), vz = coneBox.cone.z();

        if (not sx.subset(I))
            return false;

        /* Consider a curve tangent to the cone family
         * which intersects the local seed at (x,y,z)
         * and intersects the left or right face at
         * (x,y,z) + (dx,dy,dz).
         * Then x+dx is either +1 or -1, so
         * dx is x+1 or x-1,
         * dy is contained in vy*dx and
         * dz is contained in vz*dy.
         */
        Ival dx = sx+I;
        Ival dy = vy*dx;
        Ival dz = vz*dx;
        return (sy+dy).subset(I) and (sz+dz).subset(I);
    }
};

using SeedBoxes = std::vector<SeedBox>;


std::ostream& operator<<(std::ostream& out, SeedBox box) {
    ConeBox B = box.asConeBox();
    out << "SeedBox: " << B.A << endl
        << B.cone << endl
        << "seed: " << box.seed;
    return out;
}


bool allCurvesAreGood(SeedBoxes& boxes)
{
    for (auto box : boxes) {
        if (not box.curvesAreGood())
            return false;
    }
    return true;
}


/* Build a seed box around a seed.
 *
 * This uses the partially hyperbolic splitting at the center of the seed
 * and scales the unit vectors by a given scale.
 */
SeedBox buildSeedBox(Dyn f, Ival scale, Vec seed, Cone cone)
{
    Vec p = midVector(seed);
    AffineMap A(scale * splitting(f, p), p);
    return SeedBox(A, cone, seed);
}


// Build seed boxes for a fundamental domain of the 3-torus.
SeedBoxes buildSeedBoxes(Dyn f, Ival scale, int N)
{
    assert(N >= 0);
    assert(N < 100);

    // Use the cone slope intended for partial hyperbolicity testing.
    Ival a = f.directedSettings().slope * Ival(-1,1);
    Cone cone(a,a);

    auto v = partitionInterval(Ival(0,1), N);
    SeedBoxes boxes;
    for (int i = 0; i < N; ++i)
    for (int j = 0; j < N; ++j)
    for (int k = 0; k < N; ++k)
    {
        boxes.push_back(buildSeedBox(f, scale, Vec(v[i],v[j],v[k]), cone));
    }
    return boxes;
}


// Local crossing {{{1

/*****
    Here, we explain the math behind the curveCovering and
    other routines.
    Let hv = floc(v) be the image of a point v
    and assume A and p are enclosures such that
    floc(v) is in A*v + p.
    In coords, write the matrix multiplication as

    hvx = axx vx + axy vy + axz vz + px
    hvy = ayx vx + ayy vy + ayz vz + py
    hvz = azx vx + azy vy + azz vz + pz

    For curveCovering, where dim u = 1 and dim s = 2,
    We want the cube to stretch in the x coordinate and
    shrink in the y and z coordinates.

    We want to maximize |hvy| subject to
    |hvx| <= 1 and |vx|, |vy|, |vz| <= 1
    and show that |hvy| < 1 under these constraints.

    We want to maximize |hvz| under the same constraints
    and this will have similar formulas.

    Idea: if hvx, vy, vz are known, this determines vx by

    axx vx = hvx - (axy vy + axz vz + px)

    Substituting into

    hvy = ayx vx + ayy vy + ayz vz + py
        = ayx/axx (hvx - axy vy - axz vz - px) + ayy vy + ayz vz + py
        = ayx/axx hvx +
          (ayy - ayx/axx * axy) vy +
          (ayz - ayx/axx * axz) vz +
          py - ayx/axx px

    For curveCovering,
    we replace hvx, vy, vz by [-1,1] in this formula, and
    compute and check if the result is in [-1,1].

    Similarly,

    hvz = azx vx + azy vy + azz vz + pz
        = azx/axx (hvx - axy vy - axz vz - px) + azy vy + azz vz + pz
        = azx/axx hvx +
          (azy - azx/axx * axy) vy +
          (azz - azx/axx * axz) vz +
          pz - azx/axx px

    For both curveCovering and surfaceCovering,
    we replace hvx, vy, vz by [-1,1] in this formula, and
    compute and check if the result is in [-1,1].

    -----

    The surfaceCovering routine is for dim u = 2 and dim s = 1.
    To analyse this routine, define

    ||v|| = max{ |vx|, |vy| }.

    We want that
    (1) ||v|| = 1 and |vz| <= 1 imply ||hv|| > 1
    and also that
    (2) ||v|| <= 1 and |vz| <= 1 and ||hv|| = 1 imply |hvz| < 1.

    For condition (1), ||v|| = 1 implies |vx| = 1 or |vy| = 1.

    We first want to confirm that if |vx| is equal to +1 or -1
    and |vy|, |vz| <= 1, then |hvx| > 1.
    It is enough to show that if
    |vy|, |vz|, |hvz| <= 1, then |vx| < 1
    and this is verified by using restrictToPreimage within surfaceCovering.

    Next, we want to confirm that if |vy| is equal to +1 or -1
    and |hvx|, |vz| <= 1, then |hvy| > 1. In the formula

    hvy = ayx/axx hvx +
          (ayy - ayx/axx * axy) vy +
          (ayz - ayx/axx * axz) vz +
          py - ayx/axx px

    we do two tests.
    In both tests, we replace hvx and vz with [-1,1].
    In the first test, we replace vy with +1, in the second with -1.
    These tests may be written as

    hvy = rest + yterm and hvy = rest - yterm

    where

    rest = ayx/axx hvx + (ayz - ayx/axx * axz) vz + py - ayx/axx px

    and

    yterm = ayy - ayx/axx * axy.

    These tests together imply condition (1).

    Then we compute hvz as above and confirm that |hvz| < 1.

*****/

/* Enclose the preimage of a plane under a local map.
 * 
 * This returns an enclosure of all points v in [-1,1]^3
 * such that floc(v) has x-coordinate in qx.
 */
Vec restrictToPreimage(LocalMap floc, Ival qx)
{

    Ival I(-1,1);
    Mat A = floc.deriv(R);
    Vec p = floc(origin);

    /* If floc(R) does not cross [-1,1] in the first coordinate,
     * we do not restrict the domain, and just return R.
     *
     * This can happen in the anyWeakCovering function
     * when a bad choice of shift vector is chosen and
     * curveCovering will fail.
     */
    if (not qx.subset(floc(R)[0]))
        return R;

    auto axx = A[0][0], axy = A[0][1], axz = A[0][2];
    auto px = p[0];

    // Note qx = axx vx + axy vy + axz vz + px ==>
    //  axx vx = qx - axy vy - axz vz - px
    // where vy and vz are in [-1,1].
    assert(not axx.contains(0.0));
    auto vx = (qx - axy*I - axz*I - px)/axx;

    Ival J;
    bool nonEmpty = intersection(vx, I, J);
    assert(nonEmpty);

    return Vec(J, I, I);
}


/* Enclose the image intersected with a plane.
 *
 * The returned box B encloses the intersection of floc(R) with { x = qx }.
 */
Vec restrictedImage(LocalMap floc, Ival qx)
{
    Vec image = floc(restrictToPreimage(floc, qx));
    return Vec(qx, image[1], image[2]);
}


// The left and right faces of a box.
Vec  leftFace(Vec B) { return Vec(left(B[0]),  B[1], B[2]); }
Vec rightFace(Vec B) { return Vec(right(B[0]), B[1], B[2]); }


/* Test if the image floc(R) maps through R.
 * This is a C^0 covering relation with dimensions u=1 and s=2.
 */
bool curveCovering(LocalMap floc)
{
    /* We first evaluate the derivative on all of R
     * and test that axx is non-zero.
     * Once this is established, we can restrict to
     * a smaller domain J x [-1,1] x [-1,1]
     * where all intersections between R and floc^{-1}(R)
     * must occur and bound the derivative on this smaller domain.
     * Then we verify the crossing conditions there.
     */
    Ival I(-1,1);
    Mat AC = floc.deriv(R);
    if (AC[0][0].contains(0.0))
        return false;
    
    Vec subcube = restrictToPreimage(floc, I);
    Mat A = floc.deriv(subcube);
    Vec p = floc(origin);

    auto axx = A[0][0], axy = A[0][1], axz = A[0][2];
    auto ayx = A[1][0], ayy = A[1][1], ayz = A[1][2];
    auto azx = A[2][0], azy = A[2][1], azz = A[2][2];
    auto px = p[0], py = p[1], pz = p[2];

    if (axx.contains(0.0))
        return false;

    /* Test that the y-coordinate lies in I for any point where
     * the x-coordinates lies in I.
     * See the reasoning in the long comment above.
     */
    auto cy = ayx/axx;
    auto hy = cy*I + (ayy-cy*axy)*I + (ayz-cy*axz)*I + py-cy*px;
    if (not hy.subsetInterior(I))
        return false;

    // Similarly test the z-coordinate.
    auto cz = azx/axx;
    auto hz = cz*I + (azy-cz*axy)*I + (azz-cz*axz)*I + pz-cz*px;
    if (not hz.subsetInterior(I))
        return false;

    // Also test that the end faces are on opposite sides.
    Ival  left = floc( leftFace(R))[0];
    Ival right = floc(rightFace(R))[0];
    return (left < -1 and 1 < right) or (right < -1 and 1 < left);
}

/* Test if two-dimensional plaques map through.
 * 
 * This is a C^0 covering relation with dimensions u=2 and s=1.
 * See long comment above for more details.
 */
bool surfaceCovering(LocalMap floc)
{
    Ival I(-1,1);
    Mat AC = floc.deriv(R);
    if (AC[0][0].contains(0.0))
        return false;
    
    Vec subcube = restrictToPreimage(floc, I);
    Mat A = floc.deriv(subcube);
    Vec p = floc(origin);

    // Test that x-coordinate overflows the interval [-1,1].
    if (not subcube[0].subsetInterior(I))
        return false;

    auto axx = A[0][0], axy = A[0][1], axz = A[0][2];
    auto ayx = A[1][0], ayy = A[1][1], ayz = A[1][2];
    auto azx = A[2][0], azy = A[2][1], azz = A[2][2];
    auto px = p[0], py = p[1], pz = p[2];

    if (axx.contains(0.0))
        return false;

    // See long comment above.
    auto cy = ayx/axx;
    auto yterm = (ayy-cy*axy);
    auto rest = cy*I + (ayz-cy*axz)*I + py-cy*px;

    if (not disjoint(rest + yterm, I))
        return false;
    if (not disjoint(rest - yterm, I))
        return false;

    // Test the z-coordinate.
    auto cz = azx/axx;
    auto hz = cz*I + (azy-cz*axy)*I + (azz-cz*axz)*I + pz-cz*px;
    if (not hz.subsetInterior(I))
        return false;

    return true;
}


// Horseshoe verification {{{1

// Split the region V into roughly cubic boxes.
SeedBoxes buildHorseBoxes(Dyn f)
{
    Vec V = f.V();
    Ival Vx = f.Vx(), Vy = f.Vy(), Vz = f.Vz();
    Ival scale(f.settings.horseScale); 

    // Split V into roughly-cubic rectangles.
    int Nx = f.settings.horseSplit;
    int Ny = floor(Nx / (Sup(Vx) - Inf(Vx)));
    int Nz = Nx;

    Dyn f_inv = f.inverse();

    auto Px = partitionInterval(Vx, Nx);
    auto Py = partitionInterval(Vy, Ny);
    auto Pz = partitionInterval(Vz, Nz);

    SeedBoxes boxes;
    for (Ival x : Px)
    for (Ival y : Py)
    for (Ival z : Pz)
    {
        Vec seed(x, y, z);

        // Skip seeds whose forward or backward orbit immediately leaves V.
        bool stays = modIntersects(f(seed), V) and
            modIntersects(f_inv(seed), V);
        if (not stays)
            continue;

        boxes.push_back(buildSeedBox(f, scale, seed, standardCone));
    }
    return boxes;
}

/* Test if the cones given by a quadratic form are preserved. */
bool quadConeTest(LocalMap floc)
{
    Mat A = floc.deriv(R);
    Mat Q = diag(Vec(1,1,-1));

    return posdef( transpose(A)*Q*A - Q );
}


bool strongCoveringWithShift(Dyn f, Vec z, SeedBox source, SeedBox target)
{
    LocalMap floc(target.asConeBox().A, f, z, source.asConeBox().A);

    if (not surfaceCovering(floc))
        return false;

    return quadConeTest(floc);
}

// Use the local map to see if the image of one seed intersects the other
// seed.
bool checkIntersection(Dyn f, Vec z, SeedBox source, SeedBox target)
{
    LocalMap floc(target.asConeBox().A, f, z, source.asConeBox().A);

    if (disjoint(floc(source.localSeed()), target.localSeed()))
        return false;

    return true;
}

/* Determines if a strong covering exists.
 *
 * This returns false if f(source.seed) and target.seed
 * are provably disjoint on the 3-torus.
 *
 * This return true if a strong covering exists using
 * a unique choice of deck transformation on the universal cover.
 *
 * In all other cases, it triggers an assert.
 */
bool strongCovering(Dyn f, SeedBox source, SeedBox target)
{
    Vec image = f(source.seed);

    if (not modIntersects(image, target.seed))
        return false;

    Vec z = shiftVector(image, target.seed);

    if (not checkIntersection(f, z, source, target))
        return false;

    assert(strongCoveringWithShift(f, z, source, target));
    return true;
}

/* This both verifies that the invariant set in V is strongly hyperbolic
 * and constructs and returns the graph of the symbolic dynamics.
 */
Graph buildIncidenceMatrix(Dyn f)
{
    SeedBoxes boxes = buildHorseBoxes(f);

    size_t numBoxes = boxes.size();

    Graph G(numBoxes);
    for (size_t i = 0; i < numBoxes; i++)
    {
        // Give progress updates.
        if (i % 1000 == 0)
            cout << "    Verified " << i << " of " << numBoxes << " boxes." << endl;
        
        for (size_t j = 0; j < numBoxes; j++)
        {
            bool covers = strongCovering(f, boxes[i], boxes[j]);
            if (covers)
                G.addEdge(i, j);
        }
    }
    return G;
}

void verifyHorseshoe(Settings& s)
{
    cout << "Verifying horseshoe..." << endl;
    Dyn f(s, FORTH);
    Graph G = buildIncidenceMatrix(f);
    cout << "Verified horseshoe exists." << endl;
    cout << "Analyzing symbolic dynamics..." << endl;
    diagnoseTransitivity(G);
    assert(isTransitive(G));
    cout << "Verified horseshoe is transitive." << endl;
}


// Blenders, bunches, and branches {{{1

/* Bunch encodes a collection of curves of the form
 *
 * gamma : J -> R^3 with gamma(t) = (rx + t, gamma_y(t), gamma_z(t)).
 *
 * The box r = (rx, ry, rz) is mathematically a rectangle
 * with rx being a single point.
 * Computationally, rx might have a very small positive width.
 *
 * The vector u = (1, uy, uz) and
 * the interval delta = [-del, +del] are such that
 * gamma'(t) lies in u + (0, delta, delta) = (1 , uy+delta, uz+delta)
 * for all t in the domain J.
 *
 */
class Bunch {
public:
    Vec r;
    Vec u;
    Ival delta;
    Ival J;

    Bunch(Vec r, Vec u, Ival delta, Ival J)
        : r(r), u(u), delta(delta), J(J)
    {
        assert(u[0] == 1.0);
    }

    // A box defining the unstable cone.
    Vec m() { return u + Vec(Ival(0), delta, delta); }

    /* A ConeBox such that every curve the bunch is also a curve of the
     * ConeBox.
     *
     * Note that the converse does not hold as not all curves in the ConeBox
     * pass through r.
     */
    ConeBox asConeBox();
};

// Build a ConeBox such that for every curve in the bunch,
// its restriction to J is a curve in the cone box.
ConeBox coneBoxFromBunch(Bunch b, Ival J)
{
    // Ensure the given J is in the domain of the curves of the bunch.
    assert(J.subset(b.J));

    Vec r = b.r, u = b.u;
    Vec p = midVector(r);
    Cone cone(b.delta, b.delta);

    /* buildConeBox builds a cone box given by the image of an
     * axis-aligned box B under an affine map A.
     * We want all points of the form
     * r + t*v with v in the cone u + (0, dy, dz)
     * where |dy|, |dz| <= del.
     *
     * The affine map A adds p and shears by u and
     * r-p has zero for its x-coordinate.
     * we want all points of the form
     * A(r-p + t*v) with t in J and v in (1, delta, delta).
     */
    return buildConeBox(shearMap(u,p), r-p + J*cone.rect, cone);
}


ConeBox Bunch::asConeBox()
{
    // Use the entire interval on which the bunch is defined.
    Bunch& b = *this;
    return coneBoxFromBunch(b, b.J);
}

/* Branch codifies the restriction of the curves of a bunch to a subinterval.
 *
 * On the universal cover, the image f(gamma) of curves of a bunch may intersect
 * multiple different translates of the blender region V under deck
 * transformations.
 * 
 * A branch represents the restriction of curves gamma of the bunch
 * to a subinterval J of the domain of the bunch, so that the restricted
 * image curves intersect at most one such translate of V.
 *
 * A branch is valid if the images of restricted curves f circ gamma|_J
 * cross through the region V + (nx, ny, nz).
 *
 * We store the integer nx in the branch class and
 * the integers ny and nz can be determined from J and nx.
 *
 * A branch is good if it is valid and every curve f circ gamma|_J
 * has a subcurve in the blender.
 *
 */
class Branch {
public:
    Bunch b;
    Ival nx;

    // This is the restriction of the domain of the original bunch.
    Ival J;

    /* This is an interval such that for any t in J and any curve
     * gamma in the bunch if
     * 
     *     f_x(gamma(t)) = qx + nx
     *
     * then we must have t in T.
     * Here, qx = b.r[0] is the x-coordinate of the rectangle of the bunch.
     */
    Ival T;

    Branch(Bunch b, Ival nx, Ival J, Ival T)
        : b(b), nx(nx), J(J), T(T) {}

    /* A cone box containing all restricted curves.
     *
     * That is, if gamma is a curve in the bunch,
     * then its restriction to J will produce a curve in the cone box.
     */
    ConeBox asConeBox() {
        return coneBoxFromBunch(b, J);
    }

    /* A box bounding preimages of points in the qx plane.
     * 
     * This returns an axis-aligned box B such that
     * if gamma is a curve in the bunch and t in T
     * then gamma(t) lies in B.
     *
     * The definition of T ensures that if f_x(gamma(t)) = qx + nx,
     * then gamma(t) lies in the returned box B.
     */
    Vec preimageOfPlane() { return b.r + T*b.m(); }
};


/* For a bunch and a target interval,
 * find an interval L such that if
 * gamma is in the bunch and
 * the x coordinate of f(gamma(t)) is in the target,
 * then we must have t in L.
 */
Ival inverseX(Dyn f, Bunch source, Ival target)
{
    // This function relies on the definition of
    // the forward map f in terms of k.
    assert(f.way == FORTH);

    auto qx = source.r[0], ry = source.r[1], rz = source.r[2];
    auto m = source.m();
    auto my = m[1], mz = m[2];
    Ival k(f.settings.k);

    /* For our dynamical system,
     * the x-coordinate of f(qx+t, y, z) is k(qx+t)-y-z.
     * For a point gamma(t) = (qx+t, y, z)
     * we have y = ry + t*vy and z = rz + t*vz
     * for a vector (1, vy, vz) in the cone given by m = (1, my, mz).
     * Hence we are solving for t in the equation
     *
     *     k(qx+t) - (ry + t*vy) - (rz + t*vz) = target <==>
     *
     *     k*qx - ry - rz + t(k - vy - vz) = target.
     *
     *  where vy and vz are unspecified, but lie in my and mz respectively.
     */
    return (target - k*qx + ry + rz) / (k - my - mz);
}
    

// Build a branch from a choice of x-translation nx.
Branch buildBranch(Dyn f, Bunch& source, Ival nx)
{
    Ival Vx = f.Vx();

    // We don't check here if this branch is valid or not.
    Ival qx = source.r[0];

    Ival fuzz(-2e-4, 2e-4);
    Ival J = inverseX(f, source, Vx + nx) + fuzz;
    Ival T = inverseX(f, source, qx + nx);
    return Branch(source, nx, J, T);
}


/* Verify that a cone box crosses the set V.
 *
 * This only tests C^0 crossing conditions and does not look at derivatives.
 *
 * This test assumes that Vy is a fundamental domain and so does not test the
 * y coordinate.
 */
bool crossesV(Dyn f, ConeBox box)
{
    Ival Vx = f.Vx(), Vz = f.Vz();

    // Consider f composed with the affine map of the cone box.
    LocalMap floc = halfLocalMap(f, box);

    // Enclose f(A([-1,1]^3)).
    Vec fAC = floc(R);

    // Check that the image's z coordinate lies in Vz.
    if (not fAC[2].subsetInterior(Vz))
        return false;
   
    // Find an integer nx such that the box crosses Vx + nx.
    Ival nx = shiftInterval(Vx, fAC[0]);
    Ival Vnx = Vx + nx;

    // Test that the faces map to opposite sides of Vx + nx.
    Ival  left = floc( leftFace(R))[0];
    Ival right = floc(rightFace(R))[0];
    return (left < Vnx and Vnx < right) or (right < Vnx and Vnx < left);
}


// Test if the branch crosses the set V nicely.
bool validBranch(Dyn f, Branch& branch)
{
    Ival x = branch.b.r[0] + branch.J;

    Ival Vx = f.Vx();
    if (not x.subset(Vx))
        return false;

    if (not branch.T.subset(branch.J))
        return false;

    ConeBox box = branch.asConeBox();
    return crossesV(f, box);
}


// Return all valid branches for the bunch.
std::vector<Branch> allBranches(Dyn f, Bunch& source)
{
    /* Determine all possible integers that
     * could be valid as a branch. This is done
     * by considering all integers inside the x-coordinate of f(V).
     */
    Vec V = f.V();
    std::vector<Ival> nlist = intInInterval(f(V)[0]);

    std::vector<Branch> acc;
    for (auto nx : nlist) {
        Branch branch = buildBranch(f, source, nx);
        if (validBranch(f, branch))
            acc.push_back(branch);
    }
    return acc;
}


/* Test if branch curve images intersect the bunch rectangle.
 *
 * This returns false if no (restricted) curve gamma in the branch
 * has an image f(gamma) which intersects the rectangle r of the bunch.
 *
 * This returns true if the intersection cannot be ruled out.
 */
bool intersect(Dyn f, Branch& branch, Bunch& bunch)
{
    return modIntersects(f(branch.preimageOfPlane()), bunch.r);
}


bool compatibleCones(Dyn f, Branch& branch, Bunch& bunch)
{
    return coneInclusion(f, branch.asConeBox(), bunch.asConeBox());
}

// A Blender is just a finite collection of Bunch objects.
class Blender {
public:
    std::vector<Bunch> data;
};


/* Determine if every curve in the image has a subcurve in the blender.
 *
 * If this returns true, it means for every curve gamma in the source bunch,
 * the restriction f circ gamma|_J contains a curve in the blender.
 * Here, J = branch.J.
 */
bool goodBranch(Dyn f, Branch& branch, Blender& blender)
{
    for (auto beta : blender.data) {
        if (intersect(f, branch, beta) and
                not compatibleCones(f, branch, beta))
            return false;
    }
    return true;
}


/* Determine if every curve in the bunch has a subcurve whose image is in the
 * blender.
 *
 * This is done by detecting if the bunch has at least one good choice of branch.
 */
bool goodBunch(Dyn f, Bunch& bunch, Blender& blender)
{
    for (auto branch : allBranches(f, bunch))
        if (goodBranch(f, branch, blender))
            return true;
    return false;
}


/* Determine if every curve gamma in the blender has a subcurve whose image is
 * in the blender.
 *
 * This is done by testing each bunch in the blender.
 */
bool blenderInvariant(Dyn f, Blender& blender)
{
    for (auto bunch : blender.data)
        if (not goodBunch(f, bunch, blender))
            return false;
    return true;
}


// Construct the bunch corresponding to the rectangle r.
Bunch buildBunch(Dyn f, Vec r)
{
    Vec u = splitting(f, r).column(0);
    Vec uu(1.0, u[1]/u[0], u[2]/u[0]);
    double del = f.settings.bunchSlope;
    Ival J = f.Vx() - r[0];

    return Bunch(r, uu, Ival(-del, del), J);
}


/* Construct a blender as a union of bunches.
 *
 * This splits the plane P = qx times Vy times Vz
 * into a grid of nearly-square rectangles and constructs a blender
 * from each rectangle.
 */
Blender buildBlender(Dyn f)
{
    int N = f.settings.bunchSplit;
    assert(N > 0);

    Ival Vx = f.Vx(), Vy = f.Vy(), Vz = f.Vz();
    int M = floor(N / Sup(width(Vz)));

    // We use the midpoint for qx here for simplicity.
    auto qx = midpoint(Vx);
    auto y = partitionInterval(Vy, M);
    auto z = partitionInterval(Vz, N);

    Blender b;
    for (auto ry : y)
    for (auto rz : z) {
        Vec r(qx, ry, rz);
        b.data.push_back(buildBunch(f, r));
    }

    return b;
}


void verifyBlender(Settings& s)
{
    cout << "Verifying blender..." << endl;
    Dyn f(s, FORTH);
    auto blender = buildBlender(f);
    bool invariant = blenderInvariant(f, blender);
    assert(invariant);
    cout << "Verified blender is invariant" << endl;
}


// Weak partial hyperbolicity {{{1

/* These routines test for an invariant, expanding cone family.
 * In local coordinates, we use the x-coordinate to determine the length
 * of a vector, and so we only need to test expansion of the x-coordinate
 * to verify expansion. If the x-coordinate is expanded by at least a
 * constant factor above 1 at every iteration, every vector in the cone
 * must be expanded under iteration.
 */

// Test both for cone inclusion and that the local x-coordinate is expanded.
bool coneExpansion(Dyn f, ConeBox source, ConeBox target)
{
    // This does the same test as the coneInclusion() routine,
    // but also tests for expansion of the x-coordinate

    LocalMap floc(target.A, f, origin, source.A);
    Mat A = floc.deriv(R);

    // Test cone inclusion.
    if (not (A*source.cone).inside(target.cone)) {
        SAY(cone inclusion FAILED);
        TEST(source.center());
        TEST(target.center());
        TEST(source.A);
        TEST(source.enclosure());

        Ival z = source.enclosure()[2];
        int k = f.settings.k;
        Ival b = f.settings.b;
        Ival c = 2 * PI * b * cospi(2.0 * z);
        TEST(z);
        TEST(b);
        TEST(k);
        TEST(cospi(2.0*z));
        TEST(c);

        TEST(f.deriv(source.enclosure()));
        TEST(target.A);
        TEST(source.cone);
        TEST(A);
        TEST(A*source.cone);
        TEST(target.cone);

        return false;
    }

    /* A vector (1, vy, vz) in the cone is mapped
     * by the derivative, represented by A, to a vector
     * with x-coordinate axx + axy*vy + axz*vz.
     * We test that the absolute value of this vector is
     * greater than one.
     */
    auto axx = A[0][0], axy = A[0][1], axz = A[0][2];
    auto vy = source.cone.y(), vz = source.cone.z();

    bool out = (abs(axx + axy*vy + axz*vz) > 1);

    if (not out) {
        SAY(cone expansion FAILED);
        TEST(source.center());
        TEST(target.center());
        TEST(A);
    } 

    return out;
}


// How many pairs of intersecting boxes?
// This is used to debug optimizations to see if we are missing pairs.
int pairCount;


// Confirm weak PH splitting by considering all pairs of boxes.
bool slowVerifyWeakPH(Dyn f, SeedBoxes& boxes)
{
    cout << "Verifying weak partially hyperbolic splitting..." << endl;

    int N = boxes.size();
    for (int i = 0; i < N; ++i)
    {
        // This is the most time-consuming step, so we give progress updates.
        if (i % 1000 == 0)
            cout << "    Verified " << i << " of " << N << " boxes." << endl;
        
        SeedBox source = boxes[i];
        Vec image = f(source.seed);

        for (auto target : boxes)
        {
            if (not modIntersects(image, target.seed))
                continue;
            if (not coneExpansion(f, source.coneBox, target.coneBox)) {
                cout << "VERIFICATION FAILED" << endl;
                return false;
            }
            ++pairCount;
        }
    }

    cout << "Tested " << pairCount << " pairs of boxes." << endl;

    cout << "Verified weak partially hyperbolic splitting." << endl;
    return true;
}

// Confirm weak PH splitting for one source box.
bool boxWeakPH(Dyn f, int index, int split, SeedBoxes& boxes)
{
    int n = split;
    SeedBox source = boxes[index];
    Vec image = f(source.seed);

    /* Note: this optimized version assumes that boxes
     * is the result of buildSeedBoxes so that
     * runs of n*n boxes all have the same x-coord for the seed and
     * runs of n boxes all have the same y-coord where n=split.
     */
    for (int i = 0; i < n; ++i)
    {
        SeedBox& xtarget = boxes[i*n*n];
        if (not modIntersects(image[0], xtarget.seed[0]))
            continue;

        for (int j = 0; j < n; ++j)
        {
            int yindex = ((i*n)+j)*n;
            SeedBox& ytarget = boxes[yindex];
            if (not modIntersects(image[1], ytarget.seed[1]))
                continue;

            for (int k = 0; k < n; ++k)
            {
                SeedBox& target = boxes[yindex+k];

                if (not modIntersects(image[2], target.seed[2]))
                    continue;

                if (not coneExpansion(f, source.coneBox, target.coneBox)) {
                    cout << "VERIFICATION FAILED" << endl;
                    return false;
                }
                ++pairCount;
            }
        }
    }

    return true;
}

int cuberoot(int N) {
    int i;
    for (i = 0; i < 100; ++i)
        if (i*i*i == N)
            break;
    assert(i*i*i == N);
    return i;
}

/* Verify the weak PH splitting by comparing pairs of boxes.
 *
 * This assumes that boxes are in the order produced by buildSeedBoxes
 * and can skip some pairs of boxes based on the coordinates.
 *
 * A slower and simpler verification is given by slowVerifyWeakPH.
 */
bool verifyWeakPH(Dyn f, SeedBoxes& boxes)
{
    cout << "Verifying weak partially hyperbolic splitting..." << endl;

    int N = boxes.size();
    int n = cuberoot(N);

    pairCount = 0;

    for (int i = 0; i < N; ++i)
    {
        // This is the most time-consuming step, so we give progress updates.
        if (i % 1000 == 0)
            cout << "    Verified " << i << " of " << N << " boxes." << endl;
        
        bool result = boxWeakPH(f, i, n, boxes);
        if (not result)
            return false;
    }

    cout << "Tested " << pairCount << " pairs of boxes." << endl;

    cout << "Verified weak partially hyperbolic splitting." << endl;

    return true;
}


// Weak covering {{{1

// Test if one cone box weakly covers another.
bool weakCoveringWithShift(Dyn f, Vec z, ConeBox source, ConeBox target)
{
    LocalMap floc(target.A, f, z, source.A);

    if (not (floc.deriv(R)*source.cone).inside(target.cone))
        return false;

    return curveCovering(floc);
}


// Test if any integer translation produces a weak covering.
bool anyWeakCovering(Dyn f, ConeBox source, ConeBox target)
{
    auto Bs = source.enclosure();
    auto Bt = target.enclosure();
    for (Vec z : allShiftVectors(f(Bs), Bt))
        if (weakCoveringWithShift(f, z, source, target))
            return true;
    return false;
}


// A version of weakCovering with diagnostic output.
bool diagnoseWeakCovering(Dyn f, Vec z, ConeBox source, ConeBox target)
{
    SAY(diagnoseWeakCovering);
    LocalMap floc(target.A, f, z, source.A);
    TEST(floc.deriv(R));
    TEST(floc(origin));

    bool coneTest = (floc.deriv(R)*source.cone).inside(target.cone);
    TEST(coneTest);

    // Adapted from curveCovering
    Ival I(-1,1);
    Mat AC = floc.deriv(R);
    if (AC[0][0].contains(0.0))
        return false;
    
    Vec subcube = restrictToPreimage(floc, I);
    Mat A = floc.deriv(subcube);
    Vec p = floc(origin);
    TEST(AC);
    TEST(subcube);
    TEST(A);
    TEST(p);

    auto axx = A[0][0], axy = A[0][1], axz = A[0][2];
    auto ayx = A[1][0], ayy = A[1][1], ayz = A[1][2];
    auto azx = A[2][0], azy = A[2][1], azz = A[2][2];
    auto px = p[0], py = p[1], pz = p[2];

    TEST(axx.contains(0.0));
    if (axx.contains(0.0))
        return false;

    /* Test that the y-coordinate lies in I for any point where
     * the x-coordinates lies in I.
     * See the documentation above curveCovering.
     */
    auto cy = ayx/axx;
    auto hy = cy*I + (ayy-cy*axy)*I + (ayz-cy*axz)*I + py-cy*px;
    TEST(cy);
    TEST(hy);
    TEST(hy.subset(I));

    // Similarly test the z-coordinate.
    auto cz = azx/axx;
    auto hz = cz*I + (azy-cz*axy)*I + (azz-cz*axz)*I + pz-cz*px;
    TEST(cz);
    TEST(hz);
    TEST(hz.subset(I));

    Ival  left = floc( leftFace(R))[0];
    Ival right = floc(rightFace(R))[0];
    TEST(floc(leftFace(R)));
    TEST(left);
    TEST(floc(rightFace(R)));
    TEST(right);

    bool covers = (left < -1 and 1 < right) or (right < -1 and 1 < left);
    TEST(left < -1 and 1 < right);
    TEST(right < -1 and 1 < left);
    TEST(covers);

    bool out = hy.subset(I) and hz.subset(I) and covers;
    TEST(out);
    return out;
}

bool diagnoseWeakCovering(Dyn f, ConeBox source, ConeBox target)
{
    Vec p = source.center(), q = target.center();
    TEST(p);
    TEST(f(p));
    TEST(q);
    TEST(q + Ival(0.1)*R);
    Vec z = shiftVector(f(p), q + Ival(0.1)*R);
    return diagnoseWeakCovering(f, z, source, target);
}


// Output a grid of * or . for when the boxes cover the target.
void gridCover(Dyn f, SeedBoxes& boxes, ConeBox target)
{
    // Find n such that n^3 = N.
    int N = boxes.size();
    int n = cuberoot(N);
    assert(n*n*n == N);

    int hits = 0;
    int misses = 0;
    for (int i = 0; i < N; ++i) {
        if (i % (n*n) == 0)
            cout << endl << (i/(n*n)) << endl << endl;

        auto source = boxes[i];
        bool cover = anyWeakCovering(f, source.asConeBox(), target);
        cout << (cover ? '*' : '.');

        if (cover)
            ++hits;
        else
            ++misses;

        if ((i+1) % n == 0)
            cout << endl;
    }

    TEST(hits);
    TEST(misses);
}

// Test that all boxes weakly cover a given target box.
bool allBoxesCoverTarget(Dyn f, SeedBoxes& boxes, ConeBox target)
{
    for (auto source : boxes)
        if (not anyWeakCovering(f, source.asConeBox(), target))
            return false;
    return true;
}


// Fixed point {{{1

/* The following routines find a fixed point for the
 * function on the 3-torus.
 *
 * We lift to the universal cover and solve for f(v) = v
 * This means we are solving for g(v) = 0 where g(v) = f(v) - v
 * It has Jacobian Dg = Df - eye(3).
 */

// Helper routine for the Krawczyk method
Vec krawStep(Dyn f, Vec B)
{
    Mat Id = eye(3);

    // Approximate the inverse of the Jacobian at the midpoint.
    Vec p = midVector(B);
    Mat A = inverseMatrix(f.deriv(p) - Id);

    // Evaluate g at p.
    Vec gp = f(p) - p;

    // Evaluate the derivative of g on all of B.
    Mat DgB = f.deriv(B) - Id;

    // Calculate K as in Krawczyk's theorem.
    Vec K = p - A*gp + (Id-A*DgB)*(B-p);
   
    return K;
}

Vec krawFixed(Dyn f, Vec B)
{
    // Run two steps to get a closer estimate.
    Vec K = krawStep(f, B);
    K = krawStep(f, K);

    // Run more steps to get a tighter enclosure;
    for (int i = 0; i < 4; ++i) {
        Vec K1 = krawStep(f, K);
        assert(subset(K1, K));
        K = K1;
    }

    return K;
}

// Enclose a fixed point not at the origin.
Vec encloseFixedPoint(Dyn f)
{
    // Crudely estimate the location
    int k = f.settings.k;
    Ival t(0.4);
    Vec p(t, (k-2)*t, t);
    Vec B = p + Vec(Ival(-0.05, 0.05), Ival(-0.5, 0.5), Ival(-0.05, 0.05));
    Vec q = krawFixed(f, B);

    // Shift y coordinate to [0,1].
    int ny = floor(Inf(q[1]));
    Vec out(q[0], q[1]-Ival(ny), q[2]);

    return out;
}


/* Reverse the order of the v^u, v^c, and v^s vectors in a cone box.
 *
 * This is used to take a cone box constructed for f and use it in
 * a calculation for f inverse, or vice versa.
 */
ConeBox reorderCoords(ConeBox box)
{
    Mat A;
    A.column(0) = box.A.A.column(2);
    A.column(1) = box.A.A.column(1);
    A.column(2) = box.A.A.column(0);

    return ConeBox(AffineMap(A, box.A.p), box.cone);
}


/* Verify that the cone box has a unique fixed point,
 * which is hyperbolic with dim u = 1.
 */
bool hyperbolicFixedPoint(Dyn f, ConeBox box, Vec seed)
{
    /* We check both weak and strong covering to ensure
     * the local unstable manifold is a u-curve in
     * for the cones of the cone box and the cones
     * defined by quadratic forms.
     */
    if (not anyWeakCovering(f, box, box))
        return false;

    /* For simplicity, we reuse the horseshoe code, which assumes dim u = 2,
     * and so we use the inverse of the given f and reorder the coords.
     */
    SeedBox B(reorderCoords(box), seed);
    assert(B.seedIsInside());
    return strongCovering(f.inverse(), B, B);
}


// Activation {{{1

// Build a local map between two cone boxes.
LocalMap coneBoxMap(Dyn f, ConeBox source, ConeBox target)
{
    Vec p = source.center(), q = target.center();
    Vec z = shiftVector(f(p), q + Ival(0.1)*R);
    return LocalMap(target.A, f, z, source.A);
}


/* Build a target cone box so that the source cone box weakly covers it.
 *
 * The target box is centered at q.
 * The stable and unstable scales of the target box are the same as the source box.
 * The center scale is chosen as small as possible.
 * The target cone family is also chosen as small as possible.
 */
ConeBox fitBox(Dyn f, ConeBox source, Vec q)
{
    // First build a ``proto-map'' from the ConeBox to its image
    Vec protoSizes = source.sizes();
    ConeBox proto = dynamicalConeBox(f, q, protoSizes, standardCone);
    LocalMap pmap = coneBoxMap(f, source, proto);
    Vec subcube = restrictToPreimage(pmap, R[0]);
    Vec pimage = pmap(subcube);

    /* Calculate the needed sizes and build the local map.
     * This is the final local map, but we are not using the correct cones
     * for the target yet.
     */
    Ival xsize = protoSizes[0];
    Ival ysize = right(abs(pimage[1])) * protoSizes[1] + 1e-4;
    Ival zsize = protoSizes[2];

    Vec sizes(xsize, ysize, zsize);
    ConeBox proto2 = dynamicalConeBox(f, q, sizes, standardCone);
    LocalMap floc = coneBoxMap(f, source, proto2);

    // Use the derivative of the local map to calculate the new cone family.
    Cone cone = (floc.deriv(R)*source.cone).pad();
    ConeBox target = dynamicalConeBox(f, q, sizes, cone);

    assert(anyWeakCovering(f, source, target));
    return target;
}


// Translate an interval so its infimum is in [0,1).
Ival fundamentalInterval(Ival J)
{
    return J - Ival(floor(Inf(J)));
}


// Translate a point to the fundamental domain [0,1]^3
Vec fundamental(Vec v)
{
    Vec out;
    FORDIM(k)
        out[k] = fundamentalInterval(v[k]);
    return out;
}


// The image of the center of a box translated to [0,1]^3.
Vec fundImage(Dyn f, Vec B)
{
    return fundamental(midVector(f(midVector(B))));
}


// Fit a new cone box at the image of the center of the old box.
ConeBox nextBox(Dyn f, ConeBox source)
{
    return fitBox(f, source, fundImage(f, source.center()));
}


/* This attempts to build a series of cone boxes connecting from B0
 * to a point in V.
 *
 * On success, it returns B0, B1, ..., Bn where
 * B0 is the initial given box,
 * B1 is centered at p,
 * each box weakly covers the next, and
 * Bn has a center mapped by f to a point in V.
 *
 * On failure, it returns an empty list.
 */
ConeBoxes orbitToV(Dyn f, ConeBox B0, Vec p)
{
    ConeBoxes B;
    B.push_back(B0);

    ConeBox B1 = fitBox(f, B0, p);
    B.push_back(B1);

    Vec V = f.V();

    const int MAX_ITER = 8;
    for (int i = 0; i < MAX_ITER; ++i) {
        Vec q = B.back().center();

        // If the center maps into V, we've succeeded.
        if (modIntersects(f(q), V))
            return B;

        // Otherwise, add another box.
        ConeBox next = nextBox(f, B.back());
        B.push_back(next);
    }

    // Failure.
    return ConeBoxes();
}


// Find a rectangle that contains the intersection of the cone box
// with the plane at the center of the blender.
Vec intersectBlenderPlane(Dyn f, ConeBox box, Blender& blender)
{
    assert(blender.data.size() > 0);

    LocalMap floc = halfLocalMap(f, box);
    Ival qx = blender.data[0].r[0];
    Ival nx = shiftInterval(qx, floc(R)[0]);
    return restrictedImage(floc, qx+nx) - Vec(nx, 0, 0);
}

/* Determine if every curve in the ConeBox has a subcurve with image in the blender.
 *
 * This could possibly be unified with the goodBranch function.
 */
bool activatesBlender(Dyn f, ConeBox box, Blender& blender)
{
    if (not crossesV(f, box))
        return false;

    // Intersect the box with the plane at the center of the blender.
    Vec X = intersectBlenderPlane(f, box, blender);

    /* Let alpha be a curve in the cone box.
     * The crossesV test implies that f(alpha) contains a point p in X
     * and therefore p lies in some rectangle r_i associated to a bunch F_i
     * where r_i intersects X. If the cones of the cone box are mapped into
     * the cones of F_i, then f(alpha) will contain a curve in the bunch.
     *
     * Therefore, to verify the activation, we test cone compatibility for all
     * bunches whose rectangle r intersects X.
     */
    for (auto bunch : blender.data) {
        Vec r = bunch.r;
        if (not modIntersects(r, X))
            continue;

        ConeBox target = bunch.asConeBox();
        if (not coneInclusion(f, box, target))
            return false;
    }
    return true;
}


// Helper class for sampling points.
class Segment {
public:
    Vec p;
    Vec v;
    int N;

    Segment(Vec p, Vec v, int N)
        : p(p), v(v), N(N)
    {
        assert(N >= 2);
    }

    Vec sample(int i)
    {
        assert(0 <= i);
        assert(i <= N);

        // Linearly map [0,N] to [-1,1]
        double t = (2.0*i/N - 1.0);
        return p + Ival(t)*v;
    }
};

// Sample N points in the linear unstable direction of p.
Segment unstableSegment(Dyn f, Vec p, int N)
{
    Vec u = splitting(f, p).column(0);
    Ival ep(0.01);
    return Segment(p, ep*u, N);
}


// Search for a sequence of weakly covering cone boxes from the origin to the
// blender.
ConeBoxes findActivationOrbit(Dyn f, Blender& blender)
{
    // Make a box for the fixed point at the origin.
    Ival ep(0.02);
    ConeBox B0 = dynamicalConeBox(f, origin, Vec(ep,ep,ep), standardCone);

    // Confirm that this box defines a hyperbolic fixed point.
    bool hyp = hyperbolicFixedPoint(f, B0, origin);
    assert(hyp);

    // Now look at sample points
    Segment seg = unstableSegment(f, origin, 1000);
    for (int i = 0; i < seg.N; ++i) {
        Vec p = seg.sample(i);

        auto orbit = orbitToV(f, B0, p);
        if (orbit.size() == 0)
            continue;

        if (activatesBlender(f, orbit.back(), blender))
            return orbit;
    }

    // Failure, return empty vector.
    return ConeBoxes();
}

// Confirm this sequence of boxes shows the fixed point at the origin
// activates the blender.
bool confirmActivationOrbit(Dyn f, ConeBoxes B, Blender& blender)
{
    if (B.size() == 0)
        return false;

    // Confirm that the first box defines a hyperbolic fixed point.
    bool hyp = hyperbolicFixedPoint(f, B[0], origin);
    assert(hyp);

    int n = B.size();
    for (int i = 0; i < n-1; ++i)
        if (not anyWeakCovering(f, B[i], B[i+1]))
            return false;

    return activatesBlender(f, B.back(), blender);
}

void verifyActivation(Settings& s)
{
    cout << "Verifying blender and activation..." << endl;
    Dyn f(s, FORTH);
    auto blender = buildBlender(f);
    bool invariant = blenderInvariant(f, blender);
    assert(invariant);
    cout << "Verified blender is invariant." << endl;

    auto orbit = findActivationOrbit(f, blender);
    bool active = confirmActivationOrbit(f, orbit, blender);
    assert(active);
    cout << "Verified blender is activated." << endl;
}


// Shrinking cone boxes {{{1

// Build a box weakly covered by source and whose sizes are closer to target.
ConeBox shrinkStep(Dyn f, ConeBox source, ConeBox target)
{
    // This is adapted from the fitBox code. 
    Vec p = source.center();
    Ival tx = target.sizes()[0];
    Ival sy = source.sizes()[1], sz = source.sizes()[2];

    ConeBox proto = dynamicalConeBox(f, p, Vec(tx, sy, sz), standardCone);
    LocalMap pmap = coneBoxMap(f, source, proto);
    Vec subcube = restrictToPreimage(pmap, R[0]);
    Vec pimage = pmap(subcube);

    Ival xsize = tx;
    Ival ysize = Ival(1.01) * right(abs(pimage[1])) * sy;
    Ival zsize = ysize;
    Vec newSizes(xsize, ysize, zsize);
    ConeBox newBox = dynamicalConeBox(f, p, newSizes, standardCone);

    assert(anyWeakCovering(f, source, newBox));

    return newBox;
}


/* Build a chain of weak coverings at a fixed point.
 *
 * Given source and target boxes, build a sequence
 *
 * B0, B1, B2, ..., Bn
 *
 * where B0 = source, Bn = target, and each box weakly covers the next.
 * On success, the list of new boxes B1, B2, ..., B_{n-1} is returned.
 * On failure, an empty list is returned.
 *
 * This is used to take a huge box used in verifying that all unstable
 * segments of the PH splitting intersect the stable manifold of a fixed point
 * and build a chain of coverings down to a much smaller box.
 */
ConeBoxes shrink(Dyn f, ConeBox source, ConeBox target)
{
    ConeBoxes acc;

    acc.push_back(shrinkStep(f, source, target));

    for (int i = 0; i < 20; ++i) {
        ConeBox last = acc.back();
        if (anyWeakCovering(f, last, target)) {
            // Success.
            return acc;
        }

        acc.push_back(shrinkStep(f, last, target));
    }

    SAY(SHRINKING FAILED);
    diagnoseWeakCovering(f, acc.back(), target);

    // Failure.
    return ConeBoxes();
}

// Confirm the orbit returned by shrink() behaves as specified.
void verifyShrunkOrbit(Dyn f, ConeBox source, ConeBoxes orbit, ConeBox target)
{
    assert(orbit.size() > 0);
    int n = orbit.size();

    assert(anyWeakCovering(f, source, orbit[0]));
    for (int i = 0; i < n-1; ++i)
        assert(anyWeakCovering(f, orbit[i], orbit[i+1]));
    assert(anyWeakCovering(f, orbit[n-1], target));
    assert(anyWeakCovering(f, target, target));
}


// Main {{{1

/* This function verifies properties for the given diffeomorphism f, 
 * that
 * (1) f has a weak partially hyperbolic splitting Eu oplus Ecs
 * with dim Eu = 1,
 * (2) there is a hyperbolic fixed point in a dynamical box
 * centered at the given point p, and
 * (3) every unstable segment intersects the 2-dimensional stable
 * manifold of the fixed point.
 *
 * This function is called for the both forward and backward dynamics.
 */
void verifyWeak(Dyn f, Vec p)
{
    // Build both a huge box and tiny box centered at p.
    double hugeScale = f.directedSettings().hugeScale;
    Vec hugeScales(0.01, hugeScale, hugeScale);
    ConeBox huge = dynamicalConeBox(f, p, hugeScales, standardCone);

    Vec tinyScales(0.02, 0.02, 0.02);
    ConeBox tiny = dynamicalConeBox(f, p, tinyScales, standardCone);


    /* For the non-origin fixed point,
     * confirm that the point is contained in the blender region V.
     * We don't need to test the y-coordinate, as the blender region
     * in the 3-torus is of the form Vx times S^1 times Vz;
     */
    if (f.way == BACK) {
        Vec V = f.V();
        Vec E = tiny.enclosure();
        assert(E[0].subset(V[0]));
        assert(E[2].subset(V[2]));
        cout << "Verified fixed point in blender region." << endl;
    }

    // Confirm that there is a sequence of weak coverings
    // from the huge box to the tiny one.
    ConeBoxes orbit = shrink(f, huge, tiny);
    verifyShrunkOrbit(f, huge, orbit, tiny);
    cout << "Verified chain from huge box to tiny box." << endl;

    // Confirm that the tiny box defines a hyperbolic fixed point.
    bool hyp = hyperbolicFixedPoint(f, tiny, p);
    assert(hyp);
    cout << "Verified fixed point is hyperbolic." << endl;

    // Cut [0,1]^3 into N^3 smaller cubes and cover
    // each with a dynamical box.
    int N = f.directedSettings().split;
    Ival scale(f.directedSettings().scale);
    auto boxes = buildSeedBoxes(f, scale, N);

    // Confirm that the dynamical boxes are large enough.
    bool good = allCurvesAreGood(boxes);
    assert(good);
    cout << "Verified all curves are good." << endl;

    // Confirm that the boxes define a weak partially hyperbolic splitting.
    bool weakPH = verifyWeakPH(f, boxes);
    assert(weakPH);

    // Confirm that every dynamical box
    // weakly covers the huge box at the fixed point.
    bool allCover = allBoxesCoverTarget(f, boxes, huge);
    assert(allCover);
    cout << "Verified all boxes cover huge box." << endl;
}

/* Verify the weak PH splitting Eu oplus Ecs
 * and that every unstable segment intersects the
 * 2-d stable manifold of the origin.
 */
void verifyUnstable(Settings settings)
{
    cout << "Verification for forward dynamics..." << endl;
    Dyn f(settings, FORTH);
    verifyWeak(f, origin);
    cout << "All conditions for forward dynamics verified." << endl;
}

/* Verify the weak PH splitting Es oplus Ecu
 * and that every stable segment intersects the
 * 2-d unstable manifold of a fixed point q.
 */
void verifyStable(Settings settings)
{
    cout << "Verification for backward dynamics..." << endl;
    Dyn f_inv(settings, BACK);
    Vec q = encloseFixedPoint(Dyn(settings, FORTH));
    verifyWeak(f_inv, q);
    cout << "All conditions for backward dynamics verified." << endl;
}


int main()
{
    Ival b = Ival(9995, 10005)/Ival(10000);
    int k = 16; 

    Settings settings;
    settings.b = b;
    settings.k = k;

    /* For the diffeomorphism f, we have f(x,y,z) = (*,*,x)
     * where the new z coord is the old x coord.
     * If g is C^1 close to f, then the new z coord is close
     * to the old x coord. We therefore take Vz slightly larger than Vx
     * to ensure that if
     * (hx,hy,hz) = g(x,y,z) and x in Vx,
     * then hz in Vz.
     */
    Ival Vx(0.38, 0.48), Vy(0.0, 1.0);
    Ival Vz = Vx + 1e-4*Ival(-1,1);
    settings.V = Vec(Vx, Vy, Vz);

    settings.horseSplit = 40;
    settings.horseScale = 0.02;

    settings.bunchSplit = 5;
    settings.bunchSlope = 1.0/12.0;

    // For Eu oplus Ecs weak partial hyperbolicity.
    settings.forth.split = 40;
    settings.forth.slope = 0.33;
    settings.forth.scale = 0.05;
    settings.forth.hugeScale = 0.7;

    // For Es oplus Ecu weak partial hyperbolicity.
    settings.back.split = 60;
    settings.back.slope = 0.6;
    settings.back.scale = 0.07;
    settings.back.hugeScale = 0.72;

    cout << "Verifying robust transitivity for system with k = "
         << k << " and b = ["
         << Inf(b) << ", " << Sup(b) << "]." << endl;

    verifyHorseshoe(settings);

    // Not needed as verifyActivation also verifies the blender.
    //verifyBlender(settings);

    verifyActivation(settings);

    verifyUnstable(settings);

    verifyStable(settings);

    cout << "All conditions for robust transitivity verified." << endl;

    return 0;
}

