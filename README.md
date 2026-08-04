# Implement an updated version of prove_BSD for elliptic curves over Q

This is related to the abandoned pull request
https://github.com/sagemath/sage/pull/42397/files
for sage. 

It proposes a complete rewrite of the function prove_BSD instead.
This is currently a stand-alone python file, which could be adapted
and integrated into sage later.

Currently, the new function is more reliable as it specifically
uses proven theorems and avoids papers with known issues.
However, it is not yet as powerful and results in weaker
statements than the old function.

Not sure I will work on this much longer.