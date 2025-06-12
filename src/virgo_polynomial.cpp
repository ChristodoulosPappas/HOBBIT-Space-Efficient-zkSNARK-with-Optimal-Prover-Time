#include "virgo_polynomial.h"

quintuple_poly2::quintuple_poly2(){}
quintuple_poly2::quintuple_poly2(const prime_field::field_element& aa, const prime_field::field_element& bb, const prime_field::field_element& cc, const prime_field::field_element& dd, const prime_field::field_element& ee, const prime_field::field_element& ff)
{
	a = aa;
	b = bb;
	c = cc;
	d = dd;
	e = ee;
	f = ff;
}

quintuple_poly2 quintuple_poly2::operator + (const quintuple_poly2 &x) const
{
	return quintuple_poly2(a + x.a, b + x.b, c + x.c, d + x.d, e + x.e, f + x.f);
}

prime_field::field_element quintuple_poly2::eval2(const prime_field::field_element &x) const
{
	return (((((a * x) + b) * x + c) * x + d) * x + e) * x + f;
}

quadruple_poly2::quadruple_poly2(){}
quadruple_poly2::quadruple_poly2(const prime_field::field_element& aa, const prime_field::field_element& bb, const prime_field::field_element& cc, const prime_field::field_element& dd, const prime_field::field_element& ee)
{
	a = aa;
	b = bb;
	c = cc;
	d = dd;
	e = ee;
}

quadruple_poly2 quadruple_poly2::operator + (const quadruple_poly2 &x) const
{
	return quadruple_poly2(a + x.a, b + x.b, c + x.c, d + x.d, e + x.e);
}

prime_field::field_element quadruple_poly2::eval2(const prime_field::field_element &x) const
{
	return ((((a * x) + b) * x + c) * x + d) * x + e;
}

cubic_poly2::cubic_poly2(){}
cubic_poly2::cubic_poly2(const prime_field::field_element& aa, const prime_field::field_element& bb, const prime_field::field_element& cc, const prime_field::field_element& dd)
{
	a = aa;
	b = bb;
	c = cc;
	d = dd;
}

cubic_poly2 cubic_poly2::operator + (const cubic_poly2 &x) const
{
	return cubic_poly2(a + x.a, b + x.b, c + x.c, d + x.d);
}

prime_field::field_element cubic_poly2::eval2(const prime_field::field_element &x) const
{
	return (((a * x) + b) * x + c) * x + d;
}


quadratic_poly2::quadratic_poly2(){}
quadratic_poly2::quadratic_poly2(const prime_field::field_element& aa, const prime_field::field_element& bb, const prime_field::field_element& cc)
{
	a = aa;
	b = bb;
	c = cc;
}

quadratic_poly2 quadratic_poly2::operator + (const quadratic_poly2 &x) const
{
	return quadratic_poly2(a + x.a, b + x.b, c + x.c);
}

cubic_poly2 quadratic_poly2::operator * (const linear_poly2 &x) const
{
	return cubic_poly2(a * x.a, a * x.b + b * x.a, b * x.b + c * x.a, c * x.b);
}

prime_field::field_element quadratic_poly2::eval2(const prime_field::field_element &x) const
{
	return ((a * x) + b) * x + c;
}





linear_poly2::linear_poly2(){}
linear_poly2::linear_poly2(const prime_field::field_element& aa, const prime_field::field_element& bb)
{
	a = aa;
	b = bb;
}
linear_poly2::linear_poly2(const prime_field::field_element &x)
{
	a = prime_field::field_element(0);
	b = x;
}

linear_poly2 linear_poly2::operator + (const linear_poly2 &x) const
{
	return linear_poly2(a + x.a, b + x.b);
}

quadratic_poly2 linear_poly2::operator * (const linear_poly2 &x) const
{
	return quadratic_poly2(a * x.a, a * x.b + b * x.a, b * x.b);
}

prime_field::field_element linear_poly2::eval2(const prime_field::field_element &x) const
{
	return a * x + b;
}
