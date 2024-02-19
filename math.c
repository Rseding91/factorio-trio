#include <math.h>
#include <stdint.h>

// The following code is stolen from the FreeBSD math library: https://svnweb.freebsd.org/base/head/lib/msun/
// Its licence reads:
/*
 * ====================================================
 * Copyright (C) 2004 by Sun Microsystems, Inc. All rights reserved.
 *
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */

typedef union
{
  double value;
  struct
  {
    uint32_t lsw;
    uint32_t msw;
  } parts;
  struct
  {
    uint64_t w;
  } xparts;
} ieee_double_shape_type;

/* Get two 32 bit ints from a double.  */

#define EXTRACT_WORDS(ix0, ix1, d)                                \
  do {                                                            \
    ieee_double_shape_type ew_u;                                  \
    ew_u.value = (d);                                             \
    (ix0) = ew_u.parts.msw;                                       \
    (ix1) = ew_u.parts.lsw;                                       \
  } while (0)

/* Get the more significant 32 bit int from a double.  */

#define GET_HIGH_WORD(i, d)                                      \
  do {                                                            \
    ieee_double_shape_type gh_u;                                  \
    gh_u.value = (d);                                             \
    (i) = gh_u.parts.msw;                                         \
  } while (0)

/* Set the more significant 32 bits of a double from an int.  */

#define SET_HIGH_WORD(d, v)                                      \
  do {                                                            \
    ieee_double_shape_type sh_u;                                  \
    sh_u.value = (d);                                             \
    sh_u.parts.msw = (v);                                         \
    (d) = sh_u.value;                                             \
  } while (0)

/* Set the less significant 32 bits of a double from an int.  */

#define SET_LOW_WORD(d, v)                                       \
  do {                                                            \
    ieee_double_shape_type sl_u;                                  \
    sl_u.value = (d);                                             \
    sl_u.parts.lsw = (v);                                         \
    (d) = sl_u.value;                                             \
  } while (0)

/*
 * k_log1p(f):
 * Return log(1+f) - f for 1+f in ~[sqrt(2)/2, sqrt(2)].
 *
 * The following describes the overall strategy for computing
 * logarithms in base e.  The argument reduction and adding the final
 * term of the polynomial are done by the caller for increased accuracy
 * when different bases are used.
 *
 * Method :
 *   1. Argument Reduction: find k and f such that
 *			x = 2^k * (1+f),
 *	   where  sqrt(2)/2 < 1+f < sqrt(2) .
 *
 *   2. Approximation of log(1+f).
 *	Let s = f/(2+f) ; based on log(1+f) = log(1+s) - log(1-s)
 *		 = 2s + 2/3 s**3 + 2/5 s**5 + .....,
 *	         = 2s + s*R
 *      We use a special Reme algorithm on [0,0.1716] to generate
 *      a polynomial of degree 14 to approximate R The maximum error
 *	of this polynomial approximation is bounded by 2**-58.45. In
 *	other words,
 *		        2      4      6      8      10      12      14
 *	    R(z) ~ Lg1*s +Lg2*s +Lg3*s +Lg4*s +Lg5*s  +Lg6*s  +Lg7*s
 *      (the values of Lg1 to Lg7 are listed in the program)
 *	and
 *	    |      2          14          |     -58.45
 *	    | Lg1*s +...+Lg7*s    -  R(z) | <= 2
 *	    |                             |
 *	Note that 2s = f - s*f = f - hfsq + s*hfsq, where hfsq = f*f/2.
 *	In order to guarantee error in log below 1ulp, we compute log
 *	by
 *		log(1+f) = f - s*(f - R)	(if f is not too large)
 *		log(1+f) = f - (hfsq - s*(hfsq+R)).	(better accuracy)
 *
 *	3. Finally,  log(x) = k*ln2 + log(1+f).
 *			    = k*ln2_hi+(f-(hfsq-(s*(hfsq+R)+k*ln2_lo)))
 *	   Here ln2 is split into two floating point number:
 *			ln2_hi + ln2_lo,
 *	   where n*ln2_hi is always exact for |n| < 2000.
 *
 * Special cases:
 *	log(x) is NaN with signal if x < 0 (including -INF) ;
 *	log(+INF) is +INF; log(0) is -INF with signal;
 *	log(NaN) is that NaN with no signal.
 *
 * Accuracy:
 *	according to an error analysis, the error is always less than
 *	1 ulp (unit in the last place).
 *
 * Constants:
 * The hexadecimal values are the intended ones for the following
 * constants. The decimal values may be used, provided that the
 * compiler will convert from decimal to binary accurately enough
 * to produce the hexadecimal values shown.
 */

static const double
  Lg1 = 6.666666666666735130e-01,  /* 3FE55555 55555593 */
  Lg2 = 3.999999999940941908e-01,  /* 3FD99999 9997FA04 */
  Lg3 = 2.857142874366239149e-01,  /* 3FD24924 94229359 */
  Lg4 = 2.222219843214978396e-01,  /* 3FCC71C5 1D8E78AF */
  Lg5 = 1.818357216161805012e-01,  /* 3FC74664 96CB03DE */
  Lg6 = 1.531383769920937332e-01,  /* 3FC39A09 D078C69F */
  Lg7 = 1.479819860511658591e-01;  /* 3FC2F112 DF3E5244 */

/*
 * We always inline k_log1p(), since doing so produces a
 * substantial performance improvement (~40% on amd64).
 */
static inline double
k_log1p(double f)
{
  double hfsq, s, z, R, w, t1, t2;

  s = f/(2.0+f);
  z = s*s;
  w = z*z;
  t1 = w*(Lg2+w*(Lg4+w*Lg6));
  t2 = z*(Lg1+w*(Lg3+w*(Lg5+w*Lg7)));
  R = t2+t1;
  hfsq = 0.5*f*f;
  return s*(hfsq+R);
}

static const double
  two54 = 1.80143985094819840000e+16, /* 0x43500000, 0x00000000 */
  ivln10hi = 4.34294481878168880939e-01, /* 0x3fdbcb7b, 0x15200000 */
  ivln10lo = 2.50829467116452752298e-11, /* 0x3dbb9438, 0xca9aadd5 */
  log10_2hi = 3.01029995663611771306e-01, /* 0x3FD34413, 0x509F6000 */
  log10_2lo = 3.69423907715893078616e-13; /* 0x3D59FEF3, 0x11F12B36 */

static const double zero = 0.0;
static volatile double vzero = 0.0;

double trio_log10(double x)
{
  double f, hfsq, hi, lo, r, val_hi, val_lo, w, y, y2;
  int32_t i, k, hx;
  uint32_t lx;

  EXTRACT_WORDS(hx, lx, x);

  k = 0;
  if (hx < 0x00100000)                    /* x < 2**-1022  */
  {
    if (((hx&0x7fffffff)|lx) == 0)
      return -two54/vzero;            /* log(+-0)=-inf */
    if (hx < 0)
      return NAN;        /* log(-#) = NaN */
    k -= 54; x *= two54; /* subnormal number, scale up x */
    GET_HIGH_WORD(hx, x);
  }
  if (hx >= 0x7ff00000)
    return x+x;
  if (hx == 0x3ff00000 && lx == 0)
    return zero;                        /* log(1) = +0 */
  k += (hx>>20)-1023;
  hx &= 0x000fffff;
  i = (hx+0x95f64)&0x100000;
  SET_HIGH_WORD(x, hx|(i^0x3ff00000));     /* normalize x or x/2 */
  k += (i>>20);
  y = (double)k;
  f = x - 1.0;
  hfsq = 0.5*f*f;
  r = k_log1p(f);

  /* See e_log2.c for most details. */
  hi = f - hfsq;
  SET_LOW_WORD(hi, 0);
  lo = (f - hi) - hfsq + r;
  val_hi = hi*ivln10hi;
  y2 = y*log10_2hi;
  val_lo = y*log10_2lo + (lo+hi)*ivln10lo + lo*ivln10hi;

  /*
   * Extra precision in for adding y*log10_2hi is not strictly needed
   * since there is no very large cancellation near x = sqrt(2) or
   * x = 1/sqrt(2), but we do it anyway since it costs little on CPUs
   * with some parallelism and it reduces the error for many args.
   */
  w = y2 + val_hi;
  val_lo += (y2 - w) + val_hi;
  val_hi = w;

  return val_lo + val_hi;
}

static const double
  bp[] = {1.0, 1.5, },
  dp_h[] = { 0.0, 5.84962487220764160156e-01, }, /* 0x3FE2B803, 0x40000000 */
  dp_l[] = { 0.0, 1.35003920212974897128e-08, }, /* 0x3E4CFDEB, 0x43CFD006 */
  one = 1.0,
  two = 2.0,
  two53 = 9007199254740992.0,  /* 0x43400000, 0x00000000 */
  huge = 1.0e300,
  tiny = 1.0e-300,
/* poly coefs for (3/2)*(log(x)-2s-2/3*s**3 */
  L1 = 5.99999999999994648725e-01, /* 0x3FE33333, 0x33333303 */
  L2 = 4.28571428578550184252e-01, /* 0x3FDB6DB6, 0xDB6FABFF */
  L3 = 3.33333329818377432918e-01, /* 0x3FD55555, 0x518F264D */
  L4 = 2.72728123808534006489e-01, /* 0x3FD17460, 0xA91D4101 */
  L5 = 2.30660745775561754067e-01, /* 0x3FCD864A, 0x93C9DB65 */
  L6 = 2.06975017800338417784e-01, /* 0x3FCA7E28, 0x4A454EEF */
  P1 = 1.66666666666666019037e-01, /* 0x3FC55555, 0x5555553E */
  P2 = -2.77777777770155933842e-03, /* 0xBF66C16C, 0x16BEBD93 */
  P3 = 6.61375632143793436117e-05, /* 0x3F11566A, 0xAF25DE2C */
  P4 = -1.65339022054652515390e-06, /* 0xBEBBBD41, 0xC5D26BF1 */
  P5 = 4.13813679705723846039e-08, /* 0x3E663769, 0x72BEA4D0 */
  lg2 = 6.93147180559945286227e-01, /* 0x3FE62E42, 0xFEFA39EF */
  lg2_h = 6.93147182464599609375e-01, /* 0x3FE62E43, 0x00000000 */
  lg2_l = -1.90465429995776804525e-09, /* 0xBE205C61, 0x0CA86C39 */
  ovt = 8.0085662595372944372e-0017, /* -(1024-log2(ovfl+.5ulp)) */
  cp = 9.61796693925975554329e-01, /* 0x3FEEC709, 0xDC3A03FD =2/(3ln2) */
  cp_h = 9.61796700954437255859e-01, /* 0x3FEEC709, 0xE0000000 =(float)cp */
  cp_l = -7.02846165095275826516e-09, /* 0xBE3E2FE0, 0x145B01F5 =tail of cp_h*/
  ivln2 = 1.44269504088896338700e+00, /* 0x3FF71547, 0x652B82FE =1/ln2 */
  ivln2_h = 1.44269502162933349609e+00, /* 0x3FF71547, 0x60000000 =24b 1/ln2*/
  ivln2_l = 1.92596299112661746887e-08; /* 0x3E54AE0B, 0xF85DDF44 =1/ln2 tail*/

/* __ieee754_pow(x,y) return x**y
 *
 *		      n
 * Method:  Let x =  2   * (1+f)
 *	1. Compute and return log2(x) in two pieces:
 *		log2(x) = w1 + w2,
 *	   where w1 has 53-24 = 29 bit trailing zeros.
 *	2. Perform y*log2(x) = n+y' by simulating multi-precision
 *	   arithmetic, where |y'|<=0.5.
 *	3. Return x**y = 2**n*exp(y'*log2)
 *
 * Special cases:
 *	1.  (anything) ** 0  is 1
 *	2.  (anything) ** 1  is itself
 *	3.  (anything) ** NAN is NAN except 1 ** NAN = 1
 *	4.  NAN ** (anything except 0) is NAN
 *	5.  +-(|x| > 1) **  +INF is +INF
 *	6.  +-(|x| > 1) **  -INF is +0
 *	7.  +-(|x| < 1) **  +INF is +0
 *	8.  +-(|x| < 1) **  -INF is +INF
 *	9.  +-1         ** +-INF is 1
 *	10. +0 ** (+anything except 0, NAN)               is +0
 *	11. -0 ** (+anything except 0, NAN, odd integer)  is +0
 *	12. +0 ** (-anything except 0, NAN)               is +INF
 *	13. -0 ** (-anything except 0, NAN, odd integer)  is +INF
 *	14. -0 ** (odd integer) = -( +0 ** (odd integer) )
 *	15. +INF ** (+anything except 0,NAN) is +INF
 *	16. +INF ** (-anything except 0,NAN) is +0
 *	17. -INF ** (anything)  = -0 ** (-anything)
 *	18. (-anything) ** (integer) is (-1)**(integer)*(+anything**integer)
 *	19. (-anything except 0 and inf) ** (non-integer) is NAN
 *
 * Accuracy:
 *	pow(x,y) returns x**y nearly rounded. In particular
 *			pow(integer,integer)
 *	always returns the correct integer provided it is
 *	representable.
 *
 * Constants :
 * The hexadecimal values are the intended ones for the following
 * constants. The decimal values may be used, provided that the
 * compiler will convert from decimal to binary accurately enough
 * to produce the hexadecimal values shown.
 */

double trio_pow(double x, double y)
{
  double z, ax, z_h, z_l, p_h, p_l;
  double y1, t1, t2, r, s, t, u, v, w;
  int32_t i, j, k, yisint, n;
  int32_t hx, hy, ix, iy;
  uint32_t lx, ly;

  EXTRACT_WORDS(hx, lx, x);
  EXTRACT_WORDS(hy, ly, y);
  ix = hx&0x7fffffff; iy = hy&0x7fffffff;

  /* y==zero: x**0 = 1 */
  if ((iy|ly) == 0)
    return one;

  /* x==1: 1**y = 1, even if y is NaN */
  if (hx == 0x3ff00000 && lx == 0)
    return one;

  /* y!=zero: result is NaN if either arg is NaN */
  if (ix > 0x7ff00000 || ((ix == 0x7ff00000) && (lx != 0)) ||
      iy > 0x7ff00000 || ((iy == 0x7ff00000) && (ly != 0)))
    return (x+0.0)+(y+0.0);

  /* determine if y is an odd int when x < 0
   * yisint = 0	... y is not an integer
   * yisint = 1	... y is an odd int
   * yisint = 2	... y is an even int
   */
  yisint = 0;
  if (hx < 0)
  {
    if (iy >= 0x43400000)
      yisint = 2; /* even integer y */
    else if (iy >= 0x3ff00000)
    {
      k = (iy>>20)-0x3ff;        /* exponent */
      if (k > 20)
      {
        j = ly>>(52-k);
        if ((j<<(52-k)) == (int32_t) ly)
          yisint = 2-(j&1);
      }
      else if (ly == 0)
      {
        j = iy>>(20-k);
        if ((j<<(20-k)) == iy)
          yisint = 2-(j&1);
      }
    }
  }

  /* special value of y */
  if (ly == 0)
  {
    if (iy == 0x7ff00000)         /* y is +-inf */
    {
      if (((ix-0x3ff00000)|lx) == 0)
        return one;        /* (-1)**+-inf is 1 */
      else if (ix >= 0x3ff00000) /* (|x|>1)**+-inf = inf,0 */
        return (hy >= 0) ? y : zero;
      else                    /* (|x|<1)**-,+inf = inf,0 */
        return (hy < 0) ? -y : zero;
    }
    if (iy == 0x3ff00000)          /* y is  +-1 */
    {
      if (hy < 0)
        return one/x;
      else
        return x;
    }
    if (hy == 0x40000000)
      return x*x; /* y is  2 */
    if (hy == 0x3fe00000)          /* y is  0.5 */
      if (hx >= 0)       /* x >= +0 */
        return sqrt(x);
  }

  ax = fabs(x);
  /* special value of x */
  if (lx == 0)
    if (ix == 0x7ff00000 || ix == 0 || ix == 0x3ff00000)
    {
      z = ax;                 /*x is +-0,+-inf,+-1*/
      if (hy < 0)
        z = one/z;     /* z = (1/|x|) */
      if (hx < 0)
      {
        if (((ix-0x3ff00000)|yisint) == 0)
          z = (z-z)/(z-z); /* (-1)**non-int is NaN */
        else if (yisint == 1)
          z = -z;         /* (x<0)**odd = -(|x|**odd) */
      }
      return z;
    }

  /* CYGNUS LOCAL + fdlibm-5.3 fix: This used to be
      n = (hx>>31)+1;
     but ANSI C says a right shift of a signed negative quantity is
     implementation defined.  */
  n = ((uint32_t)hx>>31)-1;

  /* (x<0)**(non-int) is NaN */
  if ((n|yisint) == 0)
    return (x-x)/(x-x);

  s = one; /* s (sign of result -ve**odd) = -1 else = 1 */
  if ((n|(yisint-1)) == 0)
    s = -one; /* (-ve)**(odd int) */

  /* |y| is huge */
  if (iy > 0x41e00000)   /* if |y| > 2**31 */
  {
    if (iy > 0x43f00000)   /* if |y| > 2**64, must o/uflow */
    {
      if (ix <= 0x3fefffff)
        return (hy < 0) ? huge*huge : tiny*tiny;
      if (ix >= 0x3ff00000)
        return (hy > 0) ? huge*huge : tiny*tiny;
    }
    /* over/underflow if x is not close to one */
    if (ix < 0x3fefffff)
      return (hy < 0) ? s*huge*huge : s*tiny*tiny;
    if (ix > 0x3ff00000)
      return (hy > 0) ? s*huge*huge : s*tiny*tiny;
    /* now |1-x| is tiny <= 2**-20, suffice to compute
       log(x) by x-x^2/2+x^3/3-x^4/4 */
    t = ax-one;         /* t has 20 trailing zeros */
    w = (t*t)*(0.5-t*(0.3333333333333333333333-t*0.25));
    u = ivln2_h*t;      /* ivln2_h has 21 sig. bits */
    v = t*ivln2_l-w*ivln2;
    t1 = u+v;
    SET_LOW_WORD(t1, 0);
    t2 = v-(t1-u);
  }
  else
  {
    double ss, s2, s_h, s_l, t_h, t_l;
    n = 0;
    /* take care subnormal number */
    if (ix < 0x00100000)
    {
      ax *= two53; n -= 53; GET_HIGH_WORD(ix, ax);
    }
    n += ((ix)>>20)-0x3ff;
    j = ix&0x000fffff;
    /* determine interval */
    ix = j|0x3ff00000;          /* normalize ix */
    if (j <= 0x3988E)
      k = 0;         /* |x|<sqrt(3/2) */
    else if (j < 0xBB67A)
      k = 1;     /* |x|<sqrt(3)   */
    else
    {
      k = 0; n += 1; ix -= 0x00100000;
    }
    SET_HIGH_WORD(ax, ix);

    /* compute ss = s_h+s_l = (x-1)/(x+1) or (x-1.5)/(x+1.5) */
    u = ax-bp[k];               /* bp[0]=1.0, bp[1]=1.5 */
    v = one/(ax+bp[k]);
    ss = u*v;
    s_h = ss;
    SET_LOW_WORD(s_h, 0);
    /* t_h=ax+bp[k] High */
    t_h = zero;
    SET_HIGH_WORD(t_h, ((ix>>1)|0x20000000)+0x00080000+(k<<18));
    t_l = ax - (t_h-bp[k]);
    s_l = v*((u-s_h*t_h)-s_h*t_l);
    /* compute log(ax) */
    s2 = ss*ss;
    r = s2*s2*(L1+s2*(L2+s2*(L3+s2*(L4+s2*(L5+s2*L6)))));
    r += s_l*(s_h+ss);
    s2 = s_h*s_h;
    t_h = 3.0+s2+r;
    SET_LOW_WORD(t_h, 0);
    t_l = r-((t_h-3.0)-s2);
    /* u+v = ss*(1+...) */
    u = s_h*t_h;
    v = s_l*t_h+t_l*ss;
    /* 2/(3log2)*(ss+...) */
    p_h = u+v;
    SET_LOW_WORD(p_h, 0);
    p_l = v-(p_h-u);
    z_h = cp_h*p_h;             /* cp_h+cp_l = 2/(3*log2) */
    z_l = cp_l*p_h+p_l*cp+dp_l[k];
    /* log2(ax) = (ss+..)*2/(3*log2) = n + dp_h + z_h + z_l */
    t = (double)n;
    t1 = (((z_h+z_l)+dp_h[k])+t);
    SET_LOW_WORD(t1, 0);
    t2 = z_l-(((t1-t)-dp_h[k])-z_h);
  }

  /* split up y into y1+y2 and compute (y1+y2)*(t1+t2) */
  y1 = y;
  SET_LOW_WORD(y1, 0);
  p_l = (y-y1)*t1+y*t2;
  p_h = y1*t1;
  z = p_l+p_h;
  EXTRACT_WORDS(j, i, z);
  if (j >= 0x40900000)                              /* z >= 1024 */
  {
    if (((j-0x40900000)|i) != 0)                   /* if z > 1024 */
      return s*huge*huge;                     /* overflow */
    else if (p_l+ovt > z-p_h)
      return s*huge*huge;   /* overflow */
  }
  else if ((j&0x7fffffff) >= 0x4090cc00)          /* z <= -1075 */
  {
    if (((j-0xc090cc00)|i) != 0)           /* z < -1075 */
      return s*tiny*tiny;             /* underflow */
    else if (p_l <= z-p_h)
      return s*tiny*tiny;      /* underflow */
  }
  /*
   * compute 2**(p_h+p_l)
   */
  i = j&0x7fffffff;
  k = (i>>20)-0x3ff;
  n = 0;
  if (i > 0x3fe00000)                /* if |z| > 0.5, set n = [z+0.5] */
  {
    n = j+(0x00100000>>(k+1));
    k = ((n&0x7fffffff)>>20)-0x3ff;     /* new k for n */
    t = zero;
    SET_HIGH_WORD(t, n&~(0x000fffff>>k));
    n = ((n&0x000fffff)|0x00100000)>>(20-k);
    if (j < 0)
      n = -n;
    p_h -= t;
  }
  t = p_l+p_h;
  SET_LOW_WORD(t, 0);
  u = t*lg2_h;
  v = (p_l-(t-p_h))*lg2+t*lg2_l;
  z = u+v;
  w = v-(z-u);
  t = z*z;
  t1 = z - t*(P1+t*(P2+t*(P3+t*(P4+t*P5))));
  r = (z*t1)/(t1-two)-(w+z*w);
  z = one-(r-z);
  GET_HIGH_WORD(j, z);
  j += (n<<20);
  if ((j>>20) <= 0)
    z = scalbn(z, n); /* subnormal output */
  else
    SET_HIGH_WORD(z, j);
  return s*z;
}
