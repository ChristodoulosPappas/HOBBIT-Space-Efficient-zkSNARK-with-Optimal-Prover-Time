#ifndef __polynomial
#define __polynomial
/** @brief several univariate polynomial definitions. 
    */
#include <vector>
#include "virgo_prime_field.h"

class linear_poly2;
/**Construct a univariate cubic polynomial of f(x) = ax^3 + bx^2 + cx + d
        */
class cubic_poly2
{
public:
	prime_field::field_element a, b, c, d;
	cubic_poly2();
	cubic_poly2(const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&);
	cubic_poly2 operator + (const cubic_poly2 &) const;
	prime_field::field_element eval2(const prime_field::field_element &) const;
};

/**Construct a univariate quadratic polynomial of f(x) = ax^2 + bx + c
        */
class quadratic_poly2
{
public:
	prime_field::field_element a, b, c;
	quadratic_poly2();
	quadratic_poly2(const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&);
	quadratic_poly2 operator + (const quadratic_poly2 &) const;
	cubic_poly2 operator * (const linear_poly2 &) const;
	prime_field::field_element eval2(const prime_field::field_element &) const;
};

/**Construct a univariate linear polynomial of f(x) = ax + b
        */
class linear_poly2
{
public:
	prime_field::field_element a, b;
	linear_poly2();
	linear_poly2(const prime_field::field_element &, const prime_field::field_element &);
	linear_poly2(const prime_field::field_element &);
	linear_poly2 operator + (const linear_poly2 &) const;
	quadratic_poly2 operator * (const linear_poly2 &) const;
	prime_field::field_element eval2(const prime_field::field_element &) const;
};



/**Construct a univariate quintuple polynomial of f(x) = ax^4 + bx^3 + cx^2 + dx + e
        */
class quadruple_poly2
{
public:
	prime_field::field_element a, b, c, d, e;
	quadruple_poly2();
	quadruple_poly2(const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&);
	quadruple_poly2 operator + (const quadruple_poly2 &) const;
	prime_field::field_element eval2(const prime_field::field_element &) const;
};

/**Construct a univariate quintuple polynomial of f(x) = ax^5 + bx^4 + cx^3 + dx^2 + ex + f
        */
class quintuple_poly2
{
public:
	prime_field::field_element a, b, c, d, e, f;
	quintuple_poly2();
	quintuple_poly2(const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&, const prime_field::field_element&);
	quintuple_poly2 operator + (const quintuple_poly2 &) const;
	prime_field::field_element eval2(const prime_field::field_element &) const;
};

#endif
