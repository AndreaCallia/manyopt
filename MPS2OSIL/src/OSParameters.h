/** @file OSParameters.h
 * 
 *
 * @author  Robert Fourer,  Jun Ma, Kipp Martin, 
 * @version 1.0, 10/05/2005
 * @since   OS1.0
 *
 * \remarks
 * Copyright (C) 2005, Robert Fourer, Jun Ma, Kipp Martin,
 * Northwestern University, and the University of Chicago.
 * All Rights Reserved.
 * This software is licensed under the Common Public License. 
 * Please see the accompanying LICENSE file in root directory for terms.
 * 
 */ 
 
// CoinFinite includes <cmath> (I think) which causes a problem 
//#include<CoinFinite.hpp>

//kipp fix up the infinity issue
//kipp define OSINFINITY to COIN_DBL_MAX



#ifndef OSPARAMETERS
#define OSPARAMETERS

#include "OSConfig.h"

#include <math.h>
#ifdef HAVE_CFLOAT
# include <cfloat>
#else
# ifdef HAVE_FLOAT_H
#  include <float.h>
# endif
#endif
//#include <limits.h>
//#ifdef INFINITY //This is the definition in the ISO C99 standard.
//	#define OSINFINITY INFINITY
//#else
//	#define OSINFINITY 1e20
//#endif

#define OSINFINITY 1e30
#define OS_E_VALUE exp(1.0)
#define OS_PI_VALUE 2*asin(1.0)


#ifdef NAN 
	#define OSNAN NAN
#elif defined NaN
	#define OSNAN NaN
#elif defined nan
	#define OSNAN nan
#else	
	#define OSNAN -883849830
#endif

#ifdef DBL_MAX
	#define OSDBL_MAX DBL_MAX
#else
	#define OSDBL_MAX OSINFINITY
#endif

#ifdef INT_MAX
	#define OSINT_MAX INT_MAX
#else
	#define OSINT_MAX 2147483647
#endif

#ifndef XSLT_LOCATION
	#define XSLT_LOCATION  OSSRCDIR;
#endif

#endif
