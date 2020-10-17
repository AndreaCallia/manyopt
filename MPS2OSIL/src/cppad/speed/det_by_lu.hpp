# ifndef CPPAD_DET_BY_LU_INCLUDED
# define CPPAD_DET_BY_LU_INCLUDED

/* --------------------------------------------------------------------------
CppAD: C++ Algorithmic Differentiation: Copyright (C) 2003-07 Bradley M. Bell

CppAD is distributed under multiple licenses. This distribution is under
the terms of the 
                    Common Public License Version 1.0.

A copy of this license is included in the COPYING file of this distribution.
Please visit http://www.coin-or.org/CppAD/ for information on other licenses.
-------------------------------------------------------------------------- */
/*
$begin det_by_lu$$
$spell
	cppad
	lu
	hpp
	typedef
	const
	hpp
	Det
	CppADvector
	namespace
$$

$section Determinant Using Expansion by Lu Factorization$$

$index det_by_lu$$
$index determinant, lu factor$$
$index lu, factor determinant$$
$index factor, lu determinant$$

$head Syntax$$
$syntax%# include <cppad/speed/det_by_lu.hpp>
%$$
$syntax%det_by_lu<%Scalar%> %det%(%n%)
%$$
$syntax%%d% = %det%(%matrix%)
%$$

$head Inclusion$$
The template class $code det_by_lu$$ is defined in the $code CppAD$$
namespace by including 
the file $code cppad/speed/det_by_lu.hpp$$
(relative to the CppAD distribution directory).
It is only intended for example and testing purposes, 
so it is not automatically included by
$cref/cppad.hpp/cppad/$$.

$head Constructor$$
The syntax
$syntax%
	det_by_lu<%Scalar%> %det%(%n%)
%$$
constructs the object $italic det$$ which can be used for 
evaluating the determinant of $italic n$$ by $italic n$$ matrices
using LU factorization.

$head Scalar$$
The type $italic Scalar$$ can be any
$cref/NumericType/$$

$head n$$
The argument $italic n$$ has prototype
$syntax%
	size_t %n%
%$$

$head det$$
The syntax
$syntax%
	%d% = %det%(%matrix%)
%$$
returns the determinant of $italic matrix$$ using LU factorization.
The argument $italic matrix$$ has prototype
$syntax%
	const %Vector% &%matrix%
%$$
It must be a $italic Vector$$ with length $latex n * n$$ and with
elements of type $italic Scalar$$.
The return value $italic d$$ has prototype
$syntax%
	%Scalar% %d%
%$$

$head Vector$$
If $italic y$$ is a $italic Vector$$ object, 
it must support the syntax
$syntax%
	%y%[%i%]
%$$
where $italic i$$ has type $code size_t$$ with value less than $latex n * n$$.
This must return a $italic Scalar$$ value corresponding to the $th i$$
element of the vector $italic y$$.
This is the only requirement of the type $italic Vector$$.

$children%
	speed/example/det_by_lu.cpp%
	omh/det_by_lu_hpp.omh
%$$


$head Example$$
The file
$xref/det_by_lu.cpp/$$ 
contains an example and test of $code det_by_lu.hpp$$.
It returns true if it succeeds and false otherwise.

$head Source Code$$
The file
$cref/det_by_lu.hpp/$$ 
contains the source for this template function.


$end
---------------------------------------------------------------------------
*/
// BEGIN PROGRAM
# include <cppad/cppad.hpp>
# include <complex>

// BEGIN CppAD namespace
namespace CppAD {

// The AD complex case is used by examples by not used by speed tests 
// Must define a specializatgion of LeqZero,AbsGeq for the ADComplex case
typedef std::complex<double>     Complex;
typedef CppAD::AD<Complex>     ADComplex;
CPPAD_BOOL_UNARY(Complex,  LeqZero )
CPPAD_BOOL_BINARY(Complex, AbsGeq )

template <class Scalar>
class det_by_lu {
public:
	det_by_lu(size_t n_) : m(0), n(n_), A(n_ * n_)
	{	}

	template <class Vector>
	inline Scalar operator()(const Vector &x)
	{
		using CppAD::exp;

		Scalar         logdet;
		Scalar         det;
		int          signdet;
		size_t       i;

		// copy matrix so it is not overwritten
		for(i = 0; i < n * n; i++)
			A[i] = x[i];
 
		// comput log determinant
		signdet = CppAD::LuSolve(
			n, m, A, B, X, logdet);

		// make sure the martix is not singular
		CPPAD_ASSERT_KNOWN( 
			signdet != 0,
			"det_by_lu: matrix is singular"
		);

		// convert to determinant
		det     = Scalar( signdet ) * exp( logdet ); 

# ifdef FADBAD
		// Fadbad requires tempories to be set to constants
		for(i = 0; i < n * n; i++)
			A[i] = 0;
# endif

		return det;
	}
private:
	const size_t m;
	const size_t n;
	CppADvector<Scalar> A;
	CppADvector<Scalar> B;
	CppADvector<Scalar> X;
};
} // END CppAD namespace
// END PROGRAM
# endif
