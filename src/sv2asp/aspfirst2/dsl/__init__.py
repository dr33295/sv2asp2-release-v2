"""The specification language's front end: the grammar as data, and the signature's schema.

Stage 0 of the compiler plan (`docs/spec2rtl2/TRANSLATION.md`). Nothing here parses a `.spec`
yet -- what it establishes is that the language has ONE definition rather than two, which is
the prerequisite for a parser rather than part of one.

The reasoning, which is the same for both halves: a description that can drift from the thing
it describes is a description of nothing. The grammar printed in the methodology and the
grammar a parser is built from must be the same bytes, or one of them will quietly become
wrong -- and neither copy will look wrong, because each is internally consistent.
"""
