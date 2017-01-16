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

    **J**: Differential partial values are in some sense just a notational /
    visualization convenience, there is no further correctness criteria for them
    besides the criteria for correctness of the slices of the two partial
    values.

    **R**: essentially differential slices just follow from the observation that
    Galois connections are closed under products, and in particular f x f is a
    Galois connection if f is a Galois connection.

  * *dynamic slice* (1) - slice that works only for the specified input.

    **J**: A dynamic slice is a slice computed with respect to a specific
    input/output/run of the program.  The slicing we discuss in this paper is
    dynamic slicing.

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

    **J**: A static slice is a slice that can be computed using only the program
    and without input data or running the program.  This makes more sense in the
    context of a C-like program where the slicing criteria might be a given
    variable or set of variables.

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


Questions and answers
---------------------

  * **Q**: It seems that a slice in call-by-value semantics with holes
    corresponds exactly to those expressions that would get evaluated in a
    call-by-need/name semantics. Is that a correct observation?

    **J**: It seems plausible (and we noticed this) but I'm not sure if we've
    proved something like this.  This is partly due to the fact that we do not
    treat holes "strictly" - for example, if we replace a hole with a diverging
    expression and recompute we are not guaranteed to get the same / similar
    result.

    **R**: Backward slicing does I think correspond to call-by-name (see Biswas
    PhD thesis).  So, if you compute a backward slice, replace the holes with
    diverging expressions, and then evaluate under call-by-name, your program
    will terminate.

  * **Q**: It also seems that the whole idea of slicing bares a close
    resemblance to liveness analysis, assuming that we mark differential partial
    values as live and holes as dead (unused). Is that a correct observation?

    **J**: This also seems plausible but I'm not sure if there is a formal
    connection.

  * **Q**: What is a forward slice? What is the difference between forward and
    backward slice?

    **J**: Forward slicing (in our paper) refers to forward evaluation in the
    extended semantics with holes, starting with an environment (or expression)
    containing holes.  The idea is that forward slicing shows you what can be
    computed from a partial input /partial expression.

    **R**: I think of forward slicing as generalising CBV in the same sense that
    backward slicing generalises CBN.

  * **Q**: What is the difference between partial value and differential partial
    value?  Both values ignore part of the output to focus on a specific part of
    the value.

    **J**: A partial value is analogous to a value with some subterms "chopped
    off" (viewed as a tree).  For example, ☐::☐::3::☐.  If we want to "focus"
    just on the 3, and put the list structure into the "background" so that we
    can see what part of a computation , then we can use a differential partial
    value.  Formally, this is just a pair (p,q) whre p <= q (for example p =
    ☐::☐::☐::☐, q = ☐::☐::3::☐).

  * **Q**: What is a slicing criterion?  Isn't this just a partial value that we
    want to get?

    **J**: We define slicing criteria to be partial (or differential) values.
    But in general, slicing techniques can (and have) used many different
    criteria, for example, for C-like programs the criteria might be (sets of)
    variables.  One can also imagine slicing with respect to predicates on the
    output.  For example, we might want to slice to form an explanation why two
    parts of the output are equal, without specifying their values.

  * **Q**: Definition of a trace says it's a representation of evaluation by
    recording the evaluation > derivation as an unrolled expression. What is
    meant by "unrolled aexpression"? Also, what is > an unrolled program? (In
    the introduction: "Since the trace slices reﬂect closely the program > code
    itself, the user can read the trace slice as an unrolled program.")

   **J**: "Unrolled expression" is just a descriptive term to give an intuition
   of the trace syntax and its relation to expression syntax.  In particular, in
   many cases the trace construct is exactly the same as the expression
   construct, except that some subexpressions are traces.  The main exceptions
   are function calls, where the trace consists of the trace of the function,
   the trace of the argument, and the trace of the call.  The term "unrolled
   program" should be viewed in the same sense.

  * **Q**: Is there a difference between a program slice and a partial program?

    **J**: A partial program is a program with some subexpressions replaces with
    holes, and a program slice is a special case of a partial program that
    satisfies some slicing correctness criterion.  I think we may not be
    pedantic about this distinction in the paper, though.

  * **Q**: In section 3.1: "Γ ⊢ ρ means that ρ is a well-formed environment for
    Γ".  What does it mean that environment is well-formed for the context?  I
    don't understand the second typing judgement for `Γ ⊢ ρ`.

    **A**: For example if `Γ = [x : int, y : bool]` then `ρ = [x = 1, y = true]`
    is a well-formed environment, because values of the variables in the
    environment match types of these variables in the context.

    **Q**: The second premise is `⊢ v : τ`.  How can a variable be typed without
    a context?

    **A**: `v` is a value, not a variable, so it doesn't need a context.

  * **Q**: Section 3.2: I'm lost with encoding expressions as paths (never used
    this encoding).  How to encode this expression as a path:

    ```
    inl ((3 ⊕ 4) ⊕ (5 ⊕ 6))
    ```

    Why do I need a set of paths to represent an expression and not just a
    single path?  Is this to represent all the possible ways an expression can
    be sliced?  I don't understand the "deterministic extension" property.

    I think I understand all of the properties when thinking about expressions
    as trees, I'm just lost with the path representation.

    **J**: I don't think we actually use or rely on this representation in the
    rest of the paper.  I think it is just there for intuition regarding what
    "expressions with holes" correspond to in terms of the underlying abstract
    syntax data structures.  (I think we played with using this representation
    in earlier versions of this work but by the ICFP version we were not relying
    on it).  In this representation the ordering on partial expressions/values
    is just subset of paths, and the meet and join are intersection and union
    respectively.  Also, any non-prefix-closed set of paths in the expression
    can be represented as a differential slice.

    Abstracting away from expressions to trees generally: we can model an
    (ordered) tree as a prefix-closed subset of N* (that is, sequences of
    natural numbers).  Given a prefix-closed subset S of N*, define the
    following graph:

    G = (S, E) where E = {(w, wi) | w in S, wi in S}

    The nodes are the elements of S and the edges are the pairs (w,wi) where w
    is a sequence in S and so is wi.


Questions
---------

  * What does it mean that "program slices are defined in an
    algorithm-independent way" (Introduction, page 106, left column, 2nd
    paragraph from top)?

  * What is a Galois connection?

  * What is differential trace slice?

  * Section 3.3, paragraph directly below Figure 7: I'm not sure if I understand
    the definition of the least partial environment.  Is it an environment where
    every binding is a hole?  I completely don't understand the second paragraph
    below Fig. 7 (the one that starts with "It follows from...").

  * Section 3.4: I'm not familiar with Galois connections so I don't understand
    the discussion in paragraph starting with "Finally we are ready...".  I
    understand the Corollary 1 though.

  * I can't seem to find in the source code evaluation for partial expressions
    (with hole), shown in Figure 7 in the paper.

  * Section 4.1: "The Slicer implemention associates every trace node with a
    value".  This is `Eval.trace`.  Why is there no tracing for Holes?  My guess
    would be that a code branch with a Hole will never be taken.

  * uneval : why no code for If?

  * Is Trace also required