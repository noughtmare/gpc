# Gigaparsec

Gigaparsec (Gpc) is a library providing generalized parser combinators (Gpc)
which are able to parse all context-free grammars completely. This includes
support for left-recursion and reporting all possible parses of ambiguous
grammars.

Gigaparsec is currently only a proof of concept. Of course it needs a much more
elaborate API, but before that I want to implement disambiguation strategies.
I have also not put any effort in making this library performant yet.