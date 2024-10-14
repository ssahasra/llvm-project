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
-----------

When executing a statement ``S`` with an associated tangle ``T``, the tangle
associated with each expression in ``S`` is of the set of threads in ``T`` that
evaluate that expression.

.. note::

   Thus, in the conditional operator or in short-circuiting operators,
   convergence is determined in the "usual" way --- threads in ``T`` that
   evaluate only part of the operator do so convergently, excluding other
   threads in ``T``.

Function body
--------------

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

Statements
----------

The tangle ``T`` associated with an execution of statement ``S`` is determined
as follow:

- When ``S`` is a substatement of a parent statement ``S'`` executed with an
  associated bundle ``T'``, ``T`` is the set of threads in ``T'`` that reach
  ``S``.
- When control jumps to a labelled statement inside ``S`` (or respectively, a
  ``case`` label inside ``S``) due to the execution of a ``goto`` statement (or
  respectively, a ``switch`` statement) with an associated bundle ``T'``, ``T``
  is the set of threads in ``T'`` that reach ``S``.

.. note::

   Thus, independent of whether the statement ``S`` is entered in the "usual"
   way, or due to an unstructured jump into it, the entire statement is
   associated with the corresponding tangle. While this has no bearing on the
   substatements in ``S`` that are skipped by the jump, such a definition
   ensures that convergence is predictable in the remaining part of the
   statement ``S``.

   This includes all unstructured code such as fall-through into a ``case``
   label, a ``goto`` or ``case`` label that jumps into an iteration statement, a
   ``goto`` that jumps backwards, a ``goto`` jumps across the substatements of a
   conditional statement, etc.

Iteration statement
-------------------

When executing an iteration statement with an associated tangle ``T``, the
tangle associated with each execution the condition substatement or the body
substatement is the set of threads in ``T`` that reach the corresponding
substatement.

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
