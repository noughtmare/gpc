# Gigaparsec

Gigaparsec (Gpc) is a library providing generalized parser combinators (Gpc)
which are able to parse all context-free grammars completely. This includes
support for left-recursion and reporting all possible parses of ambiguous
grammars.

Gigaparsec is currently only a proof of concept. Of course it needs a much more
elaborate API, but before that I want to implement disambiguation strategies.
I have also not put any effort in making this library performant yet.

## Comparison with other parsing techniques

Feature                   | (atto/mega)parsec  | happy (LALR)       | Earley             | gigaparsec
--------------------------|--------------------|--------------------|--------------------|--------------------
No shift-reduce conflicts | :heavy_check_mark: | :x:                | :heavy_check_mark: | :heavy_check_mark:
Left-recusion             | :x:                | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark:
Pure Haskell              | :heavy_check_mark: | :x:                | :heavy_check_mark: | :heavy_check_mark:
Monadic                   | :heavy_check_mark: | :x:                | :x:                | :heavy_check_mark:
O(n^3) time worst-case    | :x:                | :heavy_check_mark: | :heavy_check_mark: | :x:               
O(n) time worst-case      | :x:                | :heavy_check_mark: | :x:                | :x:               
O(n) time possible        | :heavy_check_mark: | :heavy_check_mark: | :x:                | :heavy_check_mark:

