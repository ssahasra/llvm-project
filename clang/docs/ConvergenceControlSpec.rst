.. role:: convergence-control

==============================================
Language Specification for Convergence Control
==============================================

.. contents::
   :local:

Revisions
=========

- 2025/08/28 --- created

Overview
========

Some languages such as OpenCL, CUDA and HIP execute threads in groups (typicall
on a GPU) that allow efficient communication within the group using special
primitives called *convergent* operations. The outcome of a convergent operation
is sensitive to the set of threads that executes it "together", i.e.,
convergently. When control flow *diverges*, i.e., threads of the same group
follow different paths through the program, not all threads of the group may be
available to participate in this communication. This is the defining
characteristic that distinguishes convergent operations from other inter-thread
communication:

  A convergent operation involves inter-thread communication or synchronization
  that occurs outside of the memory model, where the set of threads which
  participate in communication is implicitly affected by control flow.

For example, in the following GPU compute kernel, communication during the
convergent operation is expected to occur precisely among those threads of an
implementation-defined execution scope (such as workgroup or subgroup) for
which ``condition`` is true:

.. code-block:: c++

  void example_kernel() {
      ...
      if (condition)
          convergent_operation();
      ...
  }

In a structured program there is often an intuitive and unambiguous way of
determining the threads that are expected to communicate. However, this
intuition breaks down entirely in unstructured control flow. This document
describes a formal semantics for implicit thread convergence explicit
convergence control as supported by Clang.

Thread Tangles
==============

A tangle is set of threads that can potentially communicate at a convergent
operation. This is a generalization of well-known concepts such as ``quad``,
``wave``, ``warp``, ``workgroup`` or ``block`` in OpenCL, CUDA or HIP.

Dynamically, every evaluation in the program has an associated tangle. This
tangle is derived from the static rules defined below.

Function body
--------------

The tangle associated with a function body is derived from the tangle at
each call of the function.

- If the function call has the attribute ``convergent``, then the tangle at
  the entry of the function is the same as the tangle at the function call.
- If the function call has the attribtue ``noconvergent`` then the tangle at the
  entry of the function is implementation-defined.

Statements
----------

The tangle ``InnerTangle`` associated with each statement ``InnerStatement`` is
derived from the tangle ``OuterTangle`` associated with the immediately
enclosing outer statement ``S2``. [Note: For example, ``InnerStatement`` maybe a
substatement where ``OuterStatement`` is a function body, a block, a selection
statement or an iteration statement.]

- If ``OuterStatement`` is a selection statement, then ``InnerTangle`` consists
  of all the threads in ``OuterTangle`` that reach ``InnerStatement`` after
  evaluating the condition of ``OuterStatement``.
- If ``OuterStatement`` is an iteration statement, then the ``InnerTangle`` is
  determined dynamically as follows:
  - When ``InnerStatement`` is evaluated for the first time when evaluating
    ``OuterStatement``, ``InnerTangle`` consists of all the threads in
    ``OuterTangle`` that reached ``InnerStatement``.
  - When ``InnerStatement`` is evaluated for the N+1th time when evaluating
    ``OuterStatement``, ``InnerTangle`` consists of all the threads in
    ``InnerTangle`` from the Nth evaluation that reached ``InnerStatement`` for
    this N+1th evaluation.


Conditional statements
----------------------

