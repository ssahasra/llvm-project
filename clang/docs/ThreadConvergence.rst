==================
Thread Convergence
==================

.. contents::
   :local:

Revisions
=========

- 2024/10/23 --- Created

Introduction
============

Some languages such as OpenCL, CUDA and HIP execute threads in groups (typically
on a GPU) that allow efficient communication within the group using special
primitives called *convergent* operations. The outcome of a convergent operation
is sensitive to the set of threads that execute it "together", i.e.,
`convergently`__. When control flow *diverges*, i.e., threads of the same group
follow different paths through the program, not all threads of the group may be
available to participate in this communication. This is the defining
characteristic that distinguishes convergent operations from other inter-thread
communication:

__ https://llvm.org/docs/ConvergenceAndUniformity.html

  A convergent operation involves inter-thread communication or synchronization
  that occurs outside of the memory model, where the set of threads which
  participate in communication is implicitly affected by control flow.

For example, in the following GPU compute kernel, communication during the
convergent operation is expected to occur precisely among an environment-defined
set of threads (such as workgroup or subgroup) for which ``condition`` is true:

.. code-block:: c++

  void example_kernel() {
      ...
      if (condition)
          convergent_operation();
      ...
  }

Convergence is a dynamic property of the execution. Whether two threads
convergently execute an operation is different on every execution of that
operation by those two threads. (This corresponds to `dynamic instances in LLVM
IR`__.) In a structured program, there is often an intuitive and unambiguous way
of determining the threads that are converged at a particular operation. Threads
may *diverge* at a *divergent branch*, and then *reconverge* at some later point
in the program such as the end of an enclosing statement. However, this
intuition does not work very well with unstructured control flow. In particular,
when two threads enter an `irreducible cycle`__ in the control-flow graph along
different paths, then whether they converge inside the cycle and at which point
depends on the choices made by the implementation.

__ https://llvm.org/docs/ConvergenceAndUniformity.html#threads-and-dynamic-instances
__ https://llvm.org/docs/CycleTerminology.html

This document captures convergence in terms of groups of threads called
*tangles*. Tangles symbolically represent how groups of converged threads evolve
as they pass through the control-flow graph of the program. The tangle
associated with an evaluation in the source program depends on the state of the
whole path reaching that point in the control-flow graph, including the
iterations being performed by any enclosing loops.

The intuitive picture of *convergence* is built around threads executing in
"lock step" --- a set of threads is thought of as *converged* if they are all
executing "the same sequence of instructions together". But the assumption of
lock-step execution is not necessary for describing communication at convergent
operations, and tangles *do not* assume that converged threads are executed in
lock-step.

Tangles merely represent the set of threads that must participate when a
convergent operation is executed. Threads in a tangle are not required to
execute a convergent operation "at the same time" or on the same hardware
resources. They may appear to do so in practice, but that is an implementation
detail.

The tangle associated with each operation is derived from the control-flow
reaching that point in the program. The following patterns in unstructured
control-flow are of interest:

- A ``goto`` statement that jumps backwards in the source.
- A ``goto`` statement that jumps across the *then* and *else* sides of an
  ``if`` statement.
- A ``goto`` statement that jumps across a ``case`` label.
- A ``goto`` or ``switch`` statement that jumps into a loop.
- A fall-through ``case`` in a ``switch`` statement.

Convergence can be specified easily for a ``switch-case`` fall-through, but a
combination of loop statements and jump statements can produce irreducible
cycles in the control-flow graph of the program, but such patterns are rare in
practice. Specifying the convergence of these situations is cumbersome and
likely to place unnecessary constraints on the implementation. Hence the
convergence of threads in such patterns cycles is left to the implementation.

__ https://llvm.org/docs/ConvergentOperations.html#examples-for-the-correctness-of-program-transforms

Explicit Thread Masks
---------------------

Some languages like CUDA and HIP provide convergent operations that take an
explicit threadmask as an argument. Threads are organized in groups called warps
(or waves), and a threadmask passed to a convergent operation specifies the
threads within a warp that must participate in that convergent operation. The
set of threads is explicitly specified by the programmer, rather than being
implied by the control-flow of the program. On certain hardware, such operations
also support *textually unaligned convergence*, where threads can communicate by
executing distinct occurrences of the same convergent operation in the source
code.

Tangles are neither necessary nor contradictory to the semantics of such
convergent operations with explicit threadmasks. They can be used to represent
the sets of threads that actually reach every execution of such an operation.
But the optimization constraints placed by these operations on the
implementation are different from those placed by convergent operations with
implicit threads.

Convergent Operations
=====================

A *convergent operation* is an evaluation that produces a side-effect visible to
other threads in a manner that does not depend on volatile objects, library I/O
functions or memory. The tangle associated with a convergent operation is the
set of threads that communicate at that operation.

Optimizations
-------------

In general, an implementation may not modify the control-flow reaching a
convergent operation in a way that changes the tangle associated with that
operation. But such optimizations are possible where the semantics of the
specific convergent operation allows it. The specification for convergence
control tokens in LLVM IR provides some `examples of correct transforms`__ in the
presence of convergent operations.

Thread Tangles
==============

Dynamically, every execution of a statement and evaluation of an expression has
an associated tangle. Statically, each statement or expression may be associated
with *multiple thread tangles* in the presence of unstructured control flow.

Expressions
-----------

When executing a statement ``S`` with an associated tangle ``T``, the tangle
associated with each expression in ``S`` is the set of threads in ``T`` that
evaluate that expression.

.. note::

   Thus, in the conditional operator or in short-circuiting operators,
   convergence is determined in the "usual" way --- threads in ``T`` that
   evaluate only part of the operator do so convergently, excluding other
   threads in ``T``.

Sequential Execution
--------------------

In a well-formed C++ program, statements are executed in sequence unless control
is transferred explicitly. Tangles follow this sequential execution.

When a compound statement ``S`` is executed with an associated tangle ``T``, the
tangle associated with the first substatement is ``T``.

When a substatement ``S1`` in ``S`` is executed with an associated tangle
``T1``, the tangle associated with the next substatement ``S2`` in ``S`` is the
set of threads in ``T1`` that sequentially execute ``S2`` after that execution
of ``S1``, including those threads in ``T1`` that reached the end of ``S1`` by
executing a ``break`` statement.

**[TBD: This excludes a ``goto`` that trivially jumped to ``S2`` from inside
``S1``, where ``S2`` is a labelled statement. But the ``break`` statement does
not produce such a divergence.]**

.. note::

   In other words, threads in a tangle tend to "stay converged" as control moves
   sequentially through the program, and threads that diverge tend to reconverge
   at the end of an enclosing statement.

Function body
-------------

The tangle associated with the execution of a function body is derived from the
tangle at each call of the function.

- If the function is called from outside the scope of the current program, the
  tangle associated with such a call is environment-defined. For example:

  - In an OpenCL kernel launch, the maximal set of threads that can communicate
    outside the memory model is a workgroup. Hence, a suitable choice is to
    specify that the tangle associated with the an OpenCL kernel consists of all
    the threads from a single workgroup.
  - In a C/C++ program, threads are launched independently and they can
    communicate only through the memory model. Hence the tangle associated with
    the entry point of a C/C++ program (usually the ``main`` function) consists
    of a single thread.

- If the function is called from inside the same program:

  - If the function call is *convergent*, then the tangle associated with that
    execution of the function is the same as the tangle associated with the
    function call executed by the calling function.
  - Else the tangle associated with that execution the function is
    implementation-defined.

The function body is itself a compound statement, and its substatements derive
their tangles from the tangle associated with the body.

Iteration Statement
-------------------

C++ expresses the semantics of the ``for`` statement and the ``ranged-for``
statement in terms of the ``while`` statement. Similarly, the tangle associated
with each of these statements is defined as if that statement is replaced with
the equivalent pattern using the ``while`` statement.

When executing a ``do-while`` statement with an associated tangle ``T``, the
tangle associated with the execution of the body substatement is ``T``.

When executing a ``while`` statement with an associated tangle ``T`` the tangle
associated with the execution of the condition is ``T``.

When a ``goto`` or ``switch`` statement executed with an associated tangle ``T``
transfers control to a labelled statement inside the body substatement, the
tangle associated with that execution of the body substatement is ``T``.

.. note::

   The above paragraphs specify the tangle associated with the "first" iteration
   of a loop when it is entered from outside.

When executing the condition with an associated tangle ``T``, the tangle
associated with the subsequent execution of the body substatement is the set of
threads in ``T`` that reach the body substatement.

When executing the body substatement with an associated tangle ``Tn``, the
tangle ``Tn+1`` associated with the subsequent execution of the condition is the
set of all threads in ``Tn`` that reach the condition, including those threads
that skipped the rest of the body substatement by executing a ``continue``
statement. [Explanatory note: In other words, threads that diverge at a
``continue`` statement reconverge at the end of that iteration of the loop.]

.. note::

   Thus every subsequent iteration of an iteration statement is associated with
   a distinct tangle that is derived from the tangle associated with the
   previous iteration. This precludes such tangles from being *unrelated* as
   described later.

The ``if`` Statement
--------------------

When executing an ``if`` statement with an associated tangle ``T``:

- the tangle associated with the condition is ``T``
- the tangle associated with each of the two substatements is the set of threads
  in ``T`` that reach that substatement.

.. note::

   Combined with sequential execution described above, this means that when an
   ``if`` statement is executed with an associated tangle ``T``, the threads may
   diverge to the ``then`` and ``else`` parts, but they reconverge if they reach
   the end of the statement without transferring control via a ``goto`` statement.

The ``switch`` Statement
------------------------

When a ``switch`` statement ``S`` is executed with an associated tangle ``T``
the tangle associated with each ``case`` label ``C`` is the set of threads in
``T`` that jumped to ``C``.

**[TBD: This means that a fall-through does not converge at the next label.
Allowing a fall-through needs handling of other cases such as a case jumping
into a loop, and the loop could be produced by a backwards goto.]**

The ``goto`` Statement
----------------------

When a ``goto`` statement is executed with an associated tangle ``T``, the
tangle associated with the specified labelled statement ``S`` is ``T``.

**[TBD: This means that even a simple "forward" jump in a sequence of statements
also produces divergence.]**

Divergent Jumps
===============

[This section is explanatory.]

Control transfer through a jump statement can cause threads to diverge, but the
end of a compound statement provides a natural place for these threads to
reconverge.

- A tangle that exits a statement ``S`` by executing a ``break`` statement
  trivially reconverges at the end of ``S``. ``S`` could be a ``switch``
  statement or an iteration statement.
- When a ``goto`` statement ``G`` causes a jump to a labelled statement ``L``,
  the tangle associated with ``L`` remains distinct until the end of the
  smallest statement that contains both ``G`` and ``L``.
- When a ``switch`` statement causes a jump to a ``case`` label ``C``, the
  tangle associated with that label remains distinct until the end of that
  ``switch`` statement. In particular, when a ``case`` label ``C1`` falls
  through to the next ``case`` label ``C2``, threads that jumped to ``C1`` do
  not reconverge with threads that jumped to ``C2``, until the end of the
  ``switch`` statement.

A ``goto`` statement is treated conservatively because it often produces
unstructured regions that are not easy to distinguish from "straight-line"
forward jumps in the program.

- If a ``goto`` statement jumps into the body of a loop, then that is an
  irreducible cycle in the control-flow graph.
- If a ``goto`` statement ``G1`` jumps backwards to a label statement ``L1``,
  this potentially produces a cycle in the control-flow graph. If another
  ``goto`` statement jumps to a point between ``G1`` and ``L1``, the same cycle
  may be irreducible.

.. note::

   A side-effect of this conservative treatment is that some frequently
   occurring straight-line jumps are defined to have implementation-defined
   convergence.

The control transfer at a ``switch`` statement is treated conservatively for
reasons similar to a ``goto`` statement.

- If a ``case`` label occurs inside a nested iteration statement (e.g., Duff's
  device), then that is an irreducible cycle.
- If a ``goto`` statement jumps backwards across a ``case`` fall through, then
  that may produce an irreducible cycle.

Implementation-defined Convergence
==================================

Two tangles associated with a statement are said to be *unrelated*, if neither
one of them is derived from the other by a transitive application of the above
rules.

An implementation may choose to define the union of these unrelated tangles
as the tangle associated with that statement. The tangles associated with that
statement are said to be reconverged.

When a set ``S`` of unrelated tangles is reconverged, in turn other sets of
unrelated tangles derived from those in ``S`` are also reconverged.

Maximal Convergence
-------------------

.. topic:: Definitions limited to this section:

           A *cycle* is the body of an iteration statement or the inclusive
           range of statements that occurs between a ``goto`` that jumps
           backwards and its target label.

           A *cycle entry* is the first statement in a cycle, or a labelled
           statement in a cycle which is targeted by a ``goto`` or ``switch``
           from outside the cycle.

An implementation has *maximal convergence* when every statement or expression
is associated with a single tangle. This can be achieved as follows:

1. Reconverge tangles at these points:

   1. Every ``case`` label ``C`` in a ``switch`` statement ``S`` where any cycle
      that contains ``C`` also contains ``S``.
   2. Every labelled statement ``L`` where any cycle that contains ``L`` also
      contains any ``goto`` that jumps to ``L``.

2. Iteratively choose some entry in some cycle to reconverge, until no more
   unrelated tangles remain.

For example, when a ``goto`` jumps into an iteration statement, this produces an
irreducible cycle in the control-flow graph with two entries. Operations in this
cycle have two unrelated tangles --- threads that followed the ``goto``, and
threads that entered the body through sequential execution. The implementation
may choose to reconverge the tangles at one of the entries. Trying to reconverge
at both entries may result in deadlock on an implementation where threads in a
tangle are blocked at a convergent operation until all threads in the tangle are
available for communication.

Examples
========

**[TODO: Need a lot more examples.]**

.. code-block:: c++

    void foo() {
      ... = ... ;   // S1
      ... = ... ;   // S2
      if (cond) {   // S3
        ... = ... ; // X1. This is a new sequence.
        return;
      }
      ... = ... ;   // S4
    }

In the above example, the body of the ``foo()`` is executed with the tangle
associated with that call to ``foo()``. Each substatement in the body derives
its tangle from the previous substatement. In particular, ``X1`` is the set of
threads in ``S3`` for which ``cond`` evaluated to ``true``, while ``S4`` is the
complementary set of threads in ``S3`` for which ``cond`` evaluated to ``false``.

.. code-block:: c++

    void foo() {       // S1
      if (cond1)       // S1
      {
        ... = ... ;    // S2
        goto Target1;  // S2
      }

      if (cond2)       // S3
      {                // S4
        ... = ... ;
      } else {         // S5
        Target2:
        ... = ...;
      }
    }

In the above example, the candidate tangles associated with different executions
for ``Target2``, are ``S2`` and ``S5``. They are unrelated, and whether or not
they are converged into a single execution is implementation-defined.

.. code-block:: c++

    void foo() {       // S1
      if (cond1)       // S1
      {
        ... = ... ;    // S2
        goto Target2;  // S2
      }

      for (...)        // S3
      {
        ... = ...;
        Target2:
        ... = ...;
      }
    }

In the above example, the candidate tangles associated with ``Target2`` are in
two sequences: one derived from ``S3`` and the other derived from ``S2``.
Tangles from these two sequences respectively are pairwise unrelated to each
other, and whether they are converged is implementation-defined.

Duff's device can be analyzed in the same way as the above example.

.. code-block:: c++

    void foo() {       // S1
      for (...)        // S1
      {
        ... = ...;
        if (cond)
          goto Target1;
        ... = ...;
      }

      ... = ...;
      Target1:
      ... = ...;
    }

In the above example, the tangles associated with ``Target1`` are arranged in
two sequences: those derived from the ``goto`` statement executed on different
iterations of the ``for`` loop, and those derived from threads exiting the for
loop on different iterations due to the evaluation of its conditions. As in the
previous examples, tangles from the respective sequences are unrelated, and
whether they are converged at ``Target1`` is implementation-defined.
 
