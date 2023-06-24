# Double square

All of what is said in this document is in some category $\mathbf{C}$.
The theorem just says that if the following two squares commute, then the outer part of the
rectangle also commutes.

```plantuml
X -right-> [a] Y
P -right-> [c] Q
Y -right->[b] Z 
Q -right->[d] R 
X -->[e] P
Y -->[f] Q 
Z -->[g] R
```

That is,
$$
g \circ b = d \circ f \wedge f \circ a = c \circ e
\implies
g \circ b \circ a = d \circ c \circ e
$$
