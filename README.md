# A Reasonably Exceptional Type Theory in Coq

This plugin allows to automatically translate Coq terms in such a way that
they can now use exceptions in a controlled way. This can be useful for
programming, e.g. to allow failure locally and prove after the fact that
assuming a few properties the translated term does not fail, without endangering
reduction nor polluting the type signature as a monadic translation would do.

A draft paper describing the translation can be found
[here](https://www.xn--pdrot-bsa.fr/articles/reasonably-exceptional.pdf).

# Compilation

This requires Coq 8.8. If the `COQBIN` variable is correctly set, a `make`
invokation should be enough.

Alternatively, one can install this plugin through OPAM. Assuming the Coq
repositories are available (see [the official documentation](https://github.com/coq/opam-coq-archive)),
it is enough to do the following.

```
opam pin add coq-exceptional-tt https://github.com/CoqHott/exceptional-tt.git
opam install coq-exceptional-tt
```

# Use of the plugin

The plugin adds new vernacular commands which we describe below.

## Effect Translate

```
Effect Translate GLOBAL [using GLOBAL].
```

This command translates the given global definition into the type theory with
exception. The resulting term is parameterized over the type of exceptions used.
It can be restricted to a particular exception type by adding the `using`
clause.

The resulting theory features exceptions in the Type hierarchy, which also means
it is inconsistent in general. As such, Type-living terms should be used to
write effectful, potentially exception raising-programs 

Conversely, the Prop-restricted theory is guaranteed to be exception-free and
thus consistent. This is why Prop-living properties should be used to denote
safe logical properties over the effectful programs.

## Effect Implementation

```
Effect Definition IDENT : TYPE [using GLOBAL].
```

This command opens the proof mode and ask the user to provide a proof of
TYPE in the effectful translation. When the proof is complete, the axiom IDENT
is added to Coq, a term IDENTᵉ is defined with the content of the proof, and
the axiom IDENT is registered to be mapped to IDENTᵉ through the effectful
translation.

# Examples

The repository contains a few examples in the `tests` folder.

# Caveat

Sections are not handled.

Some programs involving complex CIC features not part of the RETT source theory
will fail to be translated with either anomalies or type errors. For instance,
the translation does not handle primitive records nor universe polymorphism yet,
and notoriously tricky Prop-Type interactions like template polymorphism will
break the translation.

# License

This software is licensed under the WTFPL 2.0.
