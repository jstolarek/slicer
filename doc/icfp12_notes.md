"Functional Programs that Explain Their Work" - Notes
=====================================================

Definitions
-----------

Number in parentheses indicates section of the paper that introduces the
definition.

  * *backward slice* (1) - identify parts of a program contributing to a
    specific criterion on the output

  * *differential partial value* - like partial value, but focuses on a subvalue
    of interest.

  * *dynamic slice* (1) - slice that works only for the specified input

  * *partial program* (1) - program with some subexpressions are replaced by
    holes

  * *partial value* (1) - value where some subvalues are replaced by a hole.
    Intuitively, partial values discard parts of a value that are of no interest
    to the user.

  * *program slice* (1) - reduced program, obtained by eliminating statements
    from the original program, that produces the behaviour specified by a
    slicing criterion (ie. produces a specified partial value).

  * *slicing criteria* (3) - ?

  * *static slice* (1) - slice that makes no assumptions on the input (it works
    for any input).

  * *trace* - representation of evaluation by recording the evaluation
    derivation as an unrolled expression.

  * *trace slice* - ?


Existing work
-------------

  - Reps and Turnidge: static slicing for first-order programs

  - Biswas: slicing for strict, higher-order functional programs with a single
    slicing criterion (whole program)

  - Ochoa, Silva, Vidal: lazy, first-order programs with more flexible criteria


Slicing
-------

My understanding of a trace vs. slice is that:

  * slice is a program code that shows which parts of the code can be discarded,
    ie. are not needed to compute the specified partial value.

  * trace on the other hand records all steps of computation.  For example, it
    may show that in a given invocation of some function `f` a piece of code was
    not used but in another invocation the same piece of code can be used.


Questions
---------

  * Does a dynamic slice work only for exactly one specified input?  Or can it
    work for any input that meets a specified condition, eg. works for all
    non-empty lists?  Or is it simply a slice computed for some given input?
    What's the difference between a static and dynamic slice?

  * What is a forward slice? What is the difference between forward and backward
    slice?

  * What is the difference between partial value and differential partial value?
    Both values ignore part of the output to focus on a specific part of the
    value.

  * What does it mean that "program slices are defined in an
    algorithm-independent way" (Introduction, page 106, left column, 2nd
    paragraph from top)?

  * What is a slicing criterion?  Isn't this just a partial value that we want
    to get?

  * What is a Galois connection?

  * I don't understand definition of a trace.  What is an "unrolled expression"?

  * What is an unrolled program?  A program with inlined definitions?

  * What is the difference between slicing and liveness analysis?

  * What is differential trace slice?

  * Is there a difference between a program slice and a partial program?

  * In section 3.1: "Γ ⊢ ρ means that ρ is a well-formed environment for Γ".
    What does it mean that environment is well-formed for the context?  I don't
    understand the second typing judgement for `Γ ⊢ ρ`.  The second premise is
    `⊢ v : τ`.  How can a variable be typed without a context?

  * Why have call-by-value semantics with holes and not just call-by-need/name?

  * Section 3.2: I'm lost with encoding expressions as paths (never used this
    encoding).  How to encode this expression as a path:

    ```
    inl ((3 ⊕ 4) ⊕ (5 ⊕ 6))
    ```

    Why do I need a set of paths to represent an expression and not just a
    single path?  Is this to represent all the possible ways an expression can
    be sliced?  I don't understand the "deterministic extension" property.

    I think I understand all of the properties when thinking about expressions
    as trees, I'm just lost with the path representation.

  * Section 3.3, paragraph directly below Figure 7: I'm not sure if I understand
    the definition of the least partial environment.  Is it an environment where
    every binding is a hole?  I completely don't understand the second paragraph
    below Fig. 7 (the one that starts with "It follows from...").

  * Section 3.4: I'm not familiar with Galois connections so I don't understand
    the discussion in paragraph starting with "Finally we are ready...".  I
    understand the Corollary 1 though.
