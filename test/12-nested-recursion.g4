
grammar test12;

entry: a;
a: b c;
b: b a d | c;
c: 'c';
d: 'd';

