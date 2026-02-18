# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_variable(formula.root) or is_constant(formula.root):
        if formula.root == 'T':
            p = Formula('p')
            return Formula('|', p, Formula('~', p))
        elif formula.root == 'F':
            p = Formula('p')
            return Formula('&', p, Formula('~', p))
        return Formula(formula.root)

    if is_unary(formula.root):
        if formula.root == '~':
            return Formula('~', to_not_and_or(formula.first))

    if is_binary(formula.root):
        left = to_not_and_or(formula.first)
        right = to_not_and_or(formula.second)

        if formula.root == '&' or formula.root == '|':
            return Formula(formula.root, left, right)

        if formula.root == '->':
            return Formula('|', Formula('~', left), right)

        if formula.root == '+':
            term1 = Formula('&', left, Formula('~', right))
            term2 = Formula('&', Formula('~', left), right)
            return Formula('|', term1, term2)

        if formula.root == '<->':
            term1 = Formula('&', left, right)
            term2 = Formula('&', Formula('~', left), Formula('~', right))
            return Formula('|', term1, term2)

        if formula.root == '-&':
            return Formula('~', Formula('&', left, right))

        if formula.root == '-|':
            return Formula('~', Formula('|', left, right))

    return formula


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    formula_not_and_or = to_not_and_or(formula)

    def convert(expr: Formula) -> Formula:
        if is_variable(expr.root) or is_constant(expr.root):
            if expr.root == 'T':
                p = Formula('p')
                return Formula('~', Formula('&', p, Formula('~', p)))
            elif expr.root == 'F':
                p = Formula('p')
                return Formula('&', p, Formula('~', p))
            return expr

        if is_unary(expr.root):
            return Formula('~', convert(expr.first))

        if is_binary(expr.root):
            left = convert(expr.first)
            right = convert(expr.second)

            if expr.root == '&':
                return Formula('&', left, right)

            if expr.root == '|':
                return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))

            if expr.root in {'->', '+', '<->', '-&', '-|'}:
                return convert(to_not_and_or(expr))

        return expr

    return convert(formula_not_and_or)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    formula_not_and = to_not_and(formula)

    def convert(expr: Formula) -> Formula:
        if is_variable(expr.root):
            return expr

        if is_unary(expr.root):
            return Formula('-&', convert(expr.first), convert(expr.first))

        if is_binary(expr.root) and expr.root == '&':
            left = convert(expr.first)
            right = convert(expr.second)
            nand = Formula('-&', left, right)
            return Formula('-&', nand, nand)

        if is_constant(expr.root):
            if expr.root == 'T':
                p = Formula('p')
                nand_p = Formula('-&', p, p)
                return Formula('-&', nand_p, nand_p)
            elif expr.root == 'F':
                p = Formula('p')
                nand_p = Formula('-&', p, p)
                return Formula('-&', p, nand_p)

        return expr

    return convert(formula_not_and)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    formula_not_and_or = to_not_and_or(formula)

    def convert(expr: Formula) -> Formula:
        if is_variable(expr.root):
            return expr

        if is_constant(expr.root):
            if expr.root == 'T':
                p = Formula('p')
                return Formula('->', p, p)
            elif expr.root == 'F':
                p = Formula('p')
                return Formula('~', Formula('->', p, p))
            return expr

        if is_unary(expr.root):
            return Formula('~', convert(expr.first))

        if is_binary(expr.root):
            left = convert(expr.first)
            right = convert(expr.second)

            if expr.root == '->':
                return Formula('->', left, right)

            if expr.root == '&':
                return Formula('~', Formula('->', left, Formula('~', right)))

            if expr.root == '|':
                return Formula('->', Formula('~', left), right)

        return expr

    return convert(formula_not_and_or)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    formula_implies_not = to_implies_not(formula)

    def convert(expr: Formula) -> Formula:
        if is_variable(expr.root):
            return expr

        if expr.root == 'F':
            return Formula('F')

        if is_unary(expr.root):
            return Formula('->', convert(expr.first), Formula('F'))

        if is_binary(expr.root) and expr.root == '->':
            left = convert(expr.first)
            right = convert(expr.second)
            return Formula('->', left, right)

        return expr

    return convert(formula_implies_not)
