
grammar test09;

entry: a;
a: b c | d | ;
b: a d | c d;
c: 'c';
d: 'd';

