
grammar test10;

entry: a;
a: c b | d | ;
b: d a | d c;
c: 'c';
d: 'd';

