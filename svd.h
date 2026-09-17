/* svd.h
 *
 * This implements the bare minimum SVD calculation needed for the robust
 * transitivity code. It is based on the algorithm described in Chapter 8
 * of the Golub and Van Loan book Matrix Computations.
 *
 * Of the singular value decomposition A = U S V^T,
 * we only use the singular vectors given by the columns of V,
 * and so this header file provides a function singularVectors,
 * which given a 3 by 3 matrix of floating-point doubles,
 * returns a non-rigorous approximation of the matrix V.
 * This function has only been tested for the matrices arising in our computation,
 * and may fail when given a general 3-by-3 matrix.
 *
 * The classes Vec and Mat in the namespace linalg have
 * floating-points doubles as values, not intervals.
 *
 * This file also provides cross product and normalization routines
 * as needed to construct a non-rigorous approximation to the partially
 * hyperbolic splitting.
 */

#pragma once

#define _USE_MATH_DEFINES

#include <iostream>
#include <cmath>
#include <cassert>

using std::ostream;

namespace linalg {

// Macro to test expressions.
#ifndef SAY
#define SAY(x) \
    std::cerr << #x << std::endl;
#endif
#ifndef TEST
#define TEST(x) \
    std::cerr << #x << " = " << (x) << std::endl;
#endif

// We fix a dimension.
const int DIM = 3;

#ifndef FORDIM
#define FORDIM(k) \
    for (int k=0; k<DIM; ++k)
#endif

class Vec {
public:
    double data[DIM];
    Vec() { FORDIM(i) data[i] = 0.0; }
    double& operator[](int i) { return data[i]; }
};

inline
ostream& operator<<(ostream& out, Vec v) {
    FORDIM(j) {
        out << v[j] << "\n";
    }
    out << "\n";
    return out;
}

class Row;
class ConstRow;

class Mat {
public:
    Vec data[DIM];

    Mat() { }

    Row operator[](int index);
    ConstRow operator[](int index) const;
    Vec& col(int index) { return data[index]; }
    const Vec& col(int index) const { return data[index]; }
};

class Row {
public:
    Mat& base;
    int index;

    Row(Mat& base, int index) : base(base), index(index) {}

    double& operator[](int col) {
        return base.data[col].data[index];
    }
};

inline
Row Mat::operator[](int index) {
    return Row(*this, index);
}

class ConstRow {
public:
    const Mat& base;
    int index;

    ConstRow(const Mat& base, int index) : base(base), index(index) {}

    const double& operator[](int col) {
        return base.data[col].data[index];
    }
};

inline
ConstRow Mat::operator[](int index) const {
    return ConstRow(*this, index);
}

inline
ostream& operator<<(ostream& out, ConstRow r) {
    FORDIM(j) {
        if (j > 0)
            out << "   ";
        out << r[j];
    }
    out << "\n";
    return out;
}

inline
ostream& operator<<(ostream& out, const Mat& m) {
    out << "\n";
    FORDIM(i) {
        out << m[i];
    }
    return out;
}

inline
Mat transpose(const Mat& A) {
    Mat B;
    FORDIM(i) FORDIM(j)
        B[i][j] = A[j][i];
    return B;
}

inline
Mat operator+(const Mat& A, const Mat& B) {
    Mat C;
    FORDIM(i) FORDIM(j)
        C[i][j] += A[i][j] + B[i][j];
    return C;
}

inline
Mat operator-(const Mat& A, const Mat& B) {
    Mat C;
    FORDIM(i) FORDIM(j)
        C[i][j] += A[i][j] - B[i][j];
    return C;
}

inline
Mat operator*(double c, const Mat& A) {
    Mat B;
    FORDIM(i) FORDIM(j)
        B[i][j] = c*A[i][j];
    return B;
}

inline
Mat operator*(const Mat& A, const Mat& B) {
    Mat C;
    FORDIM(i) FORDIM(j) FORDIM(k)
        C[i][j] += A[i][k] * B[k][j];
    return C;
}

// Minimal SVD Implementation

/* The Wilkinson shift,
 * an eigenvalue of the symmetric matrix
 *     a b
 *     b d
 */
inline
double wilkinsonShift(double a, double b, double d) {

    double diff = (a - d) / 2.0;
    double h = std::sqrt(diff*diff+b*b);

    if (diff >= 0)
        return d - (b*b) / (diff + h);
    else 
        return d + (b*b) / (-diff + h);
}

class Rotation {
public:
    /* Encode the orthogonal matrix
     *     c -s
     *     s  c
     */
    double c, s;

    // Build a rotation taking (a,b) to (*,0).
    Rotation(double a, double b) {
        double w = 1.0/std::sqrt(a*a+b*b);
        c =  w*a;
        s = -w*b;
    }

    // Return the first coordinate of rotating (a,b).
    double first(double a, double b) {
        return c*a - s*b;
    }

    // Return the second coordinate of rotating (a,b).
    double second(double a, double b) {
        return s*a + c*b;
    }

    // Rotate (a,b) in place.
    void apply(double& a, double& b) {
        double x = first(a,b), y = second(a,b);
        a = x; b = y;
    }

    // Rotate (a,b) in place to (*,0).
    // This zeros the second coordinate without checking if it should be zero.
    void applyZero(double& a, double& b) {
        a = first(a,b);
        b = 0.0;
    }

    // Rotate vectors in place.
    void apply(Vec& u, Vec& v) {
        FORDIM(k)
            apply(u[k], v[k]);
    }

    // Rotate (a,b) into a new location.
    void assign(double& x, double& y, double a, double b) {
        x = first(a,b);
        y = second(a,b);
    }

};

/* Complete the second half of a QR iteration step.
 *
 * This takes S from the form
 *
 *     * * *
 *     0 * *
 *     0 * *
 *
 * to bidiagonal form
 *
 *     * * 0
 *     0 * *
 *     0 0 *
 *
 */
inline
void lasthalf(Mat& S, Mat& V)
{
    // Do a column operation to zero S[0][2].
    {
        Rotation R(S[0][1], S[0][2]);
        R.applyZero(S[0][1], S[0][2]);
        R.apply(S[1][1], S[1][2]);
        R.apply(S[2][1], S[2][2]);
        R.apply(V.col(1), V.col(2));
    }

    // Do a row operation to zero S[2][1].
    {
        Rotation R(S[1][1], S[2][1]);
        // S[1][0] and S[2][0] are already zero.
        R.applyZero(S[1][1], S[2][1]);
        R.apply(S[1][2], S[2][2]);
    }
}



/* Apply rotations to convert A into bidiagonal form S.
 *
 * This assumes that S and V are given as zero matrices.
 *
 * This routine has the same result as copying A to S,
 * setting V to the identity,
 * then applying Givens rotation matrices to S to put
 * it into bidiagonal form.
 * Column rotations are applied to both S and V.
 * Row rotations are only applied to S.
 */
inline
void bidiagonalize(Mat& S, Mat& V, const Mat& A) {

    FORDIM(k)
        V[k][k] = 1.0;

    // First, fill the top two rows of S with
    // a rotation of the top two rows of A.
    {
        Rotation R(A[0][0], A[1][0]);
        S[0][0] = R.first(A[0][0], A[1][0]); // S[1][0] already set to zero.
        for (int k = 1; k < 3; ++k)
            R.assign(S[0][k], S[1][k], A[0][k], A[1][k]);
    }

    // Then rotate the top row of S with
    // the last row of A.
    {
        Rotation R(S[0][0], A[2][0]);
        S[0][0] = R.first(S[0][0], A[2][0]); // S[2][0] already set to zero.
        for (int k = 1; k < 3; ++k)
            R.assign(S[0][k], S[2][k], S[0][k], A[2][k]);
    }

    // Now all infomation from A has been extracted and S is in the form
    //     * * *
    //     0 * *
    //     0 * *

    // The next operations are common with QR iteration.
    lasthalf(S, V);

    // Now S is in the bidiagonal form
    //     * * 0
    //     0 * *
    //     0 0 *
}

inline
void qrstep(Mat& S, Mat& V, double shift)
{
    // Determine the rotation of the matrix
    // T = S^T S - shift I
    // which would zero the (0,1) entry of T.
    // Then apply it as a column operation.
    {
        double s00 = S[0][0], s01 = S[0][1];
        Rotation R(s00*s00 - shift, s00*s01);
        R.apply(S[0][0], S[0][1]);
        R.apply(S[1][0], S[1][1]);
        // S[2][0] and S[2][1] are both zero.
        R.apply(V.col(0), V.col(1));
    }

    // The matrix S is now in the form
    //     * * 0
    //     + * *
    //     0 0 *
    //
    // Apply a row operation to zero S[1][0].
    {
        Rotation R(S[0][0], S[1][0]);
        R.applyZero(S[0][0], S[1][0]);
        R.apply(S[0][1], S[1][1]);
        R.apply(S[0][2], S[1][2]);
    }

    // The matrix is now in the form
    //     * * +
    //     0 * *
    //     0 0 *
    
    lasthalf(S, V);
}

/* Do a QR iteration step for the top-left 2-by-2 matrix. */
inline
void step22(Mat& S, Mat& V, double shift)
{
    // Determine the rotation of the matrix
    // T = S^T S - shift I
    // which would zero the (0,1) entry of T.
    // Then apply it as a column operation to S and V.
    {
        double s00 = S[0][0], s01 = S[0][1];
        Rotation R(s00*s00 - shift, s00*s01);
        R.apply(S[0][0], S[0][1]);
        R.apply(S[1][0], S[1][1]);
        // S[2][0] and S[2][1] are both zero.
        R.apply(V.col(0), V.col(1));
    }

    // The matrix S is now in the form
    //     * * 0
    //     + * *
    //     0 0 *
    //
    // Apply a row operation to zero S[1][0].
    {
        Rotation R(S[0][0], S[1][0]);
        R.applyZero(S[0][0], S[1][0]);
        R.apply(S[0][1], S[1][1]);
        // Don't rotate S[0][2] and S[1][2].
        // We're assuming S[0][2] is near zero.
    }
}

inline
void sort2(Mat& S, Mat &V, int i, int j)
{
    if (std::abs(S[i][i]) < std::abs(S[j][j])) {
        double x = S[i][i]; S[i][i] = S[j][j]; S[j][j] = x;
        Vec u = V.col(i); V.col(i) = V.col(j); V.col(j) = u;
    }
}

inline
void sortValues(Mat& S, Mat& V)
{
    sort2(S, V, 0, 1);
    sort2(S, V, 0, 2);
    sort2(S, V, 1, 2);
}

// Calculate the V matrix of the SVD A = U S V^T.
inline
Mat singularVectors(const Mat& A) {

    Mat S, V;

    bidiagonalize(S, V, A);

    for (int i = 0; i < 5; ++i) {
        double b = S[0][1], d = S[1][1], e = S[1][2], f = S[2][2];
        double shift = wilkinsonShift(b*b+d*d, d*e, e*e+f*f);
        qrstep(S, V, shift);
    }
        
    for (int i = 0; i < 2; ++i) {
        double a = S[0][0], b = S[0][1], d = S[1][1];
        double shift = wilkinsonShift(a*a, a*b, b*b+d*d);
        step22(S, V, shift);
    }

    sortValues(S, V);

    return V;
}

// Various other needed non-rigorous routines.

inline
Vec operator-(Vec v) {
    Vec out;
    FORDIM(i)
        out[i] = -v[i];
    return out;
}

// Non-rigorous cross-product calculation.
inline
Vec cross(Vec u, Vec v) {
    Vec out;
    out[0] = u[1]*v[2]-u[2]*v[1];
    out[1] = u[2]*v[0]-u[0]*v[2];
    out[2] = u[0]*v[1]-u[1]*v[0];
    return out;
}

// Unit vector in the direction of v.
inline
Vec normalise(Vec v) {
    Vec out;
    double x = v[0], y = v[1], z = v[2];
    double s = 1.0 / std::sqrt(x*x+y*y+z*z);
    out[0] = s*x; out[1] = s*y; out[2] = s*z;
    return out;
}

} // namespace linalg
