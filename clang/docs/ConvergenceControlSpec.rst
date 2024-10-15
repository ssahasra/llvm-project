.. role:: convergence-control

==============================================
Language Specification for Convergence Control
==============================================

.. contents::
   :local:

Revisions
=========

- 2024/10/14 --- Created

Overview
========

Some languages such as OpenCL, CUDA and HIP execute threads in groups (typically
on a GPU) that allow efficient communication within the group using special
primitives called *convergent* operations. The outcome of a convergent operation
is sensitive to the set of threads that execute it "together", i.e.,
convergently. When control flow *diverges*, i.e., threads of the same group
follow different paths through the program, not all threads of the group may be
available to participate in this communication. This is the defining
characteristic that distinguishes convergent operations from other inter-thread
communication:

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

But convergence is a dynamic property of the execution. In a structured program
there is often an intuitive and unambiguous way of determining the threads that
are expected to communicate. However, this intuition breaks down in unstructured
control flow. This document captures the possible dynamic convergence in terms
of groups of threads called *tangles*.

Thread Tangles
==============

A tangle is the set of threads that communicate at a convergent operation.
Dynamically, every execution of a statement and evaluation of an expression has
an associated tangle. Statically, each statement or expression may be associated
with *multiple thread tangles* in the presence of unstructured control flow.

In a structured program, the tangle associated with the execution of each
substatement is simply the set of threads that reach it from the tangle
associated with the parent statement. However, the tangle associated with a
statement that occurs inside an unstructured region of code cannot be determined
statically from the source code. For example, when a ``goto`` jumps backwards in
the source or jumps into an iteration statement, the set of threads that are
converged at the target label cannot be determined statically.

This document provides the constraints that determine the of candidate tangles
associated with the possible executions of each statement.

Expressions
===========

When executing a statement ``S`` with an associated tangle ``T``, the tangle
associated with each expression in ``S`` is of the set of threads in ``T`` that
evaluate that expression.

.. note::

   Thus, in the conditional operator or in short-circuiting operators,
   convergence is determined in the "usual" way --- threads in ``T`` that
   evaluate only part of the operator do so convergently, excluding other
   threads in ``T``.

Sequential Execution
====================

When a compound statement ``S1`` is executed with an associated tangle ``T1``, the
tangle associated with the first substatement is ``T1``.

When a statement ``S1`` is executed with an associated tangle ``T1``, the tangle
associated with the statement ``S2`` executed next in sequence after ``S1`` is
the set of threads in ``T1`` that reach the end of ``S1``.

.. note::

   In other words, threads in a tangle tend to "stay converged" as control moves
   sequentially through the program. This is broken only when control is
   transferred out of a statement by a ``goto``, forming an entirely new
   sequence of execution.

Function body
=============

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

Iteration statement
===================

When executing the body substatement with an associated tangle ``Tn``, the
tangle ``Tn+1`` associated with the end of the body substatement is the set of
all threads in ``Tn`` that reach the end, including those threads that
transferred control to the end by executing a ``continue`` statement.
[Explanatory note: In other words, a ``continue`` statement does not produce
divergence within the iteration statement.]

The tangle associated with the subsequent execution of the condition
substatement and the body substatement is the set of threads in ``Tn+1`` that
reach that substatement.

The ``for`` Statement
---------------------

.. note::

   Thus every subsequent iteration of an iteration statement is associated with
   a distinct tangle that is derived from the tangle associated with the
   previous statement. This precludes such tangles from being *unrelated* as
   described later.

   The condition substatement and the body substatement need to be distinguished
   in order to have a well-defined tangle in the case where control is
   transferred directly into the body substatement via a jump.

The tangle associated with the end of the iteration statement is the set of all
threads in ``T`` that reached the end, including those threads that transferred
control to the end by executing a ``break`` statement. [Explanatory note: In
other words, a ``break`` statement does not produce divergence after the
iteration statement.]

The ``if`` Statement
--------------------

When an ``if`` statement is executed with an associated tangle ``T``, the tangle
associated with the condition is ``T`` and the tangle associated with each of
the two substatements is the set of threads in ``T`` that reach that statement.

.. note::

   Combined with sequential execution described above, this means that when an
   ``if`` statement is executed with an associated tangle ``T``, the threads may
   diverge to the ``then`` and ``else`` parts, but they reconverge if they reach
   the end of the statement without transferring control via a ``goto`` statement.

The ``switch`` Statement
------------------------

When a ``switch`` statement executed with an associated tangle ``T`` transfers
control to a ``case`` label ``S``, the tangle associated with that execution of
``S`` is the set of threads in ``T`` that jumped to ``S``.

The ``goto`` Statement
----------------------

When a ``goto`` statement executed with an associated tangle ``T`` transfers
control to a labelled statement ``S``, the tangle associated with that execution
of ``S`` is the set of threads in ``T`` that jumped to ``S``.

Implementation-defined Convergence
----------------------------------

Two tangles associated with a statement are said to be *unrelated*, if neither
one of them is derived from the other by a transitive application of the above
rules. Whether or not two unrelated tangles *converge* to form a single tangle
is implementation defined.

.. note::

   For example, when a ``goto`` jumps into an iteration statement, this produces
   an irreducible cycle in the control-flow graph with two entries. The
   implementation may convert this cycle into a natural loop by adding a new
   header block. In that case, all threads entering that natural loop must
   converge at the header on every iteration.


Examples
--------

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
 
