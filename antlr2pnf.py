#!/usr/bin/env python3
#
# Copyright 2018 Nick Sumner
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

# The normalization performed by this script is described in
# Perses: Syntax-Guided Program Reduction
# Chengnian Sun, Yuanbo Li, Qirun Zhang, Tianxiao Gu, Zhendong Su
# ICSE 2018
#
# Minor modifications were made to the process, as the printed algorithm
# doesn't quite produce grammars in PNF form. Errors in this implementation
# are solely my own. Where possible, variable names match the names in the
# paper.

import itertools
import collections
import datetime
import networkx as nx
from argparse import ArgumentParser

from antlr4 import *
from ANTLRv4Lexer import ANTLRv4Lexer
from ANTLRv4Parser import ANTLRv4Parser
from ANTLRv4ParserVisitor import ANTLRv4ParserVisitor


def get_all_leaves(tree):
    leaves = []

    def dfs_leaf_helper(subtree):
        if isinstance(subtree, TerminalNode):
            leaves.append(subtree)
        elif subtree.children:
            for child in subtree.children:
                dfs_leaf_helper(child)
        else:
            print('ERROR', repr(subtree))
    dfs_leaf_helper(tree)
    return leaves


def get_tree_as_string(tree, sep=''):
    return sep.join(str(x) for x in get_all_leaves(tree))


def flatten(iterable):
    return tuple(x for xs in iterable for x in xs)


def ends_with(haystack, needle):
    if len(haystack) < len(needle):
        return False
    return haystack[-len(needle):] == needle


def starts_with(haystack, needle):
    if len(haystack) < len(needle):
        return False
    return haystack[:len(needle)] == needle


class GrammarBuilder:
    LEFT = 1
    RIGHT = 2

    def __init__(self):
        self.nonterminals = {}
        self.dedup = {}
        self.fresh_id = 0

    def to_antlr_string(self):
        def rule_text(rule):
            return ' '.join(rule)

        chunks = ['{0}\n  : {1}\n  ;\n'.format(name,
                  '\n  | '.join(rule_text(rule) for rule in rules))
                  for name, rules in sorted(self.nonterminals.items())]
        return '\n'.join(chunks)

    # Note, this computes the PNF for L(G)-ε
    # Since we don't care about the empty string, this is fine.
    def to_pnf(self, old_start_symbol, new_start='pnf_start'):
        self.add_nonterminal(new_start, [(old_start_symbol,)])
        self.eliminate_epsilon()
        self.prune_unreachable(new_start)
        self.normalize(self.LEFT)
        self.normalize(self.RIGHT)
        self.eliminate_simple_unit_rules()
        self.prune_unreachable(new_start)

    def eliminate_epsilon(self):
        null = set(name for name, rules in self.nonterminals.items()
                   if all(len(rule) == 0 for rule in rules))
        nullable = set(name for name, rules in self.nonterminals.items()
                       if any(len(rule) == 0 for rule in rules))
        # Compute the fixed point of the nullable set
        old_size = 0
        while len(nullable) != old_size:
            old_size = len(nullable)
            nullable.update(name for name, rules in self.nonterminals.items()
                            if any(all(term in nullable for term in rule)
                                   for rule in rules))

        def propagate(rule):
            terms = [[(term,)] + ([()] if term in nullable else [])
                     for term in rule if term not in null]
            return tuple(tuple(itertools.chain.from_iterable(rule))
                         for rule in itertools.product(*terms))

        # First compute the effects of propagating empty strings
        self.nonterminals = {name: tuple(x for rule in rhs
                                         for x in propagate(rule)
                                         if x)
                             for name, rhs in self.nonterminals.items()}
        # Then remove all empty rules.
        self.nonterminals = {name: rules
                             for name, rules in self.nonterminals.items()
                             if rules}

    def prune_unreachable(self, start):
        reachable = set()

        def dfs_helper(name):
            if name[-1] in ('?', '*', '+'):
                name = name[:-1]
            if name in self.nonterminals and name not in reachable:
                reachable.add(name)
                for term in {t for r in self.nonterminals[name] for t in r}:
                    dfs_helper(term)
        dfs_helper(start)
        self.nonterminals = {name: rules
                             for name, rules in self.nonterminals.items()
                             if name in reachable}

    def eliminate_simple_unit_rules(self):
        def non_unit(symbol):
            # Our approach to quantification just concatenates the quantifier
            # with the existing symbol name. Simplifying through the quantifier
            # requires peeling it off and then adding it back on.
            quantifier = ''
            if symbol[-1] in ('?', '*', '+'):
                symbol, quantifier = symbol[:-1], symbol[-1]
            if symbol not in self.nonterminals:
                return symbol + quantifier
            while True:
                try:
                    ((next_symbol,),) = self.nonterminals[symbol]
                    self.nonterminals[next_symbol]
                    symbol = next_symbol
                except (KeyError, ValueError):
                    return symbol + quantifier

        self.nonterminals = {name: tuple(tuple(map(non_unit, rule))
                                         for rule in rules)
                             for name, rules in self.nonterminals.items()}

    def normalize(self, direction):
        digraph = nx.DiGraph()
        for name, derivations in self.nonterminals.items():
            for derivation in derivations:
                symbol, remainder = self.directed_split(direction, derivation)
                if symbol in self.nonterminals.keys():
                    digraph.add_edge(name, symbol)

        for scc in sorted(nx.strongly_connected_components(digraph)):
            to_replace = {name: self.nonterminals[name] for name in scc}
            transformed = self.transform(direction, to_replace)
            quantified = self.quantifier(direction, transformed)
            for name in scc:
                self.nonterminals.pop(name)
            self.nonterminals.update(quantified)

        self.nonterminals = self.separate_quantified(self.nonterminals)

    def transform(self, direction, grammar):
        # Instead of a explicit fixpoint computation, we use Paull's algorithm
        # (also part of GNF conversion) for removing the indirect recursion.
        # See: Removing Left Recursion from Context-Free Grammars, Robert Moore.
        def to_rules(rule):
            symbol, remainder = self.directed_split(direction, rule)
            if symbol not in grammar or id_to_name[j] != symbol:
                return (rule,)
            else:
                return tuple(self.directed_merge(direction, inlined, remainder)
                             for inlined in grammar[symbol])

        id_to_name = {i: name for i, name in enumerate(grammar.keys())}
        for i in range(len(grammar)):
            for j in range(i):
                name = id_to_name[i]
                grammar[name] = flatten(map(to_rules, grammar[name]))
        return grammar

    def quantifier(self, direction, grammar):
        def add_plus(rule):
            before, starred, after = self.star_split(rule)
            if starred not in grammar or len(grammar[starred]) > 1:
                return rule
            (starred_rhs,) = grammar[starred]
            cleaned = self.remove_repeat(direction, before, starred_rhs, after)
            if cleaned is not None:
                before, after = cleaned
                base = 'pnf_plus_' + nonterminal
                u2_rhs = (starred_rhs,)
                u2, add_u2 = self.make_fresh_nonterminal(base, u2_rhs)
                u1_rhs = ((u2 + '+',),)
                u1, add_u1 = self.make_fresh_nonterminal(base, u1_rhs)
                if add_u2:
                    fresh_rules[u2] = u2_rhs
                if add_u1:
                    fresh_rules[u1] = u1_rhs
                return before + (u1,) + after
            else:
                return rule

        for nonterminal in list(grammar.keys()):
            self.introduce_star(direction, grammar, nonterminal)
            rules = grammar[nonterminal]
            fresh_rules = {}

            # NOTE: This list is required for *both* eager evaluation & mutation
            rules = list(map(add_plus, rules))
            rule_indices = list(range(len(rules)))
            rule_indices.sort(key=lambda x: len(rules[x]))
            print(datetime.datetime.now(),
                  'Computing Options (?). This can take some time.',
                  'You may try rerunning the script for better RNG.')
            # This next section can certainly be done more efficiently.
            # However, just rerunning the script usually solves the problem, so
            # it isn't really a priority.
            for i in rule_indices:
                if not rules[i]:
                    continue
                for j in range(i):
                    if not rules[j] or len(rules[i]) >= len(rules[j]):
                        continue
                    prefix, suffix = self.wrap_split(rules[j], rules[i])
                    if prefix == None:
                        continue
                    base = 'pnf_option_' + nonterminal
                    u4_rhs = (rules[j][len(prefix):-len(suffix)],)
                    u4, add_u4 = self.make_fresh_nonterminal(base, u4_rhs)
                    u3_rhs = ((u4 + '?',),)
                    u3, add_u3 = self.make_fresh_nonterminal(base, u3_rhs)
                    if add_u4:
                        fresh_rules[u4] = u4_rhs
                    if add_u3:
                        fresh_rules[u3] = u3_rhs
                    rules[i] = None
                    rules[j] = None
                    rules[min(i,j)] = prefix + (u3,) + suffix
                    break

            rules = tuple(rule for rule in rules if rule is not None)
            grammar[nonterminal] = rules
            grammar.update(fresh_rules)
        return grammar

    def introduce_star(self, direction, grammar, nonterminal):
        rules = grammar[nonterminal]
        if nonterminal == 'b': print('START', rules)
        A = set()
        B = set()
        for rule in rules:
            symbol, remainder = self.directed_split(direction, rule)
            if symbol == nonterminal:
                A.add(remainder)
            else:
                B.add(rule)

        # If there were no recursive rules, then the rest is unnecessary.
        if len(A) == 0:
            return
        assert len(B) != 0, "Recursion without base cases is not handled."

        rules = []
        new_forms = {}
        base = 'pnf_star_' + nonterminal
        u2_rhs = tuple(A)
        u2, add_u2 = self.make_fresh_nonterminal(base, u2_rhs)
        if add_u2:
            new_forms[u2] = u2_rhs
        for b in B:
            # NOTE: The original algorithm uses a fresh u1 here.
            # This is inconsistent with quantifier identification, so I just
            # separate quantifiers out later.
            rules.append(self.directed_merge(direction, b, (u2 + '*',)))
        grammar[nonterminal] = rules
        grammar.update(new_forms)
        if nonterminal == 'b': print('FINISH', rules)

    def separate_quantified(self, grammar):
        fresh_rules = {}
        BASE = 'pnf_separate_'
        for nonterminal, rules in grammar.items():
            def promote_quantified(symbol):
                if not symbol[-1] in ('*', '+', '?'):
                    return symbol
                base = BASE + nonterminal
                u1_rhs = ((symbol,),)
                u1, add_u1 = self.make_fresh_nonterminal(base, u1_rhs)
                if add_u1:
                    fresh_rules[u1] = u1_rhs
                return u1
            grammar[nonterminal] = tuple(tuple(map(promote_quantified, rule))
                                         if len(rule) != 1 else rule
                                         for rule in rules)
        grammar.update(fresh_rules)
        return grammar

    def star_split(self, rule):
        for i, element in enumerate(rule):
            if element[-1] == '*':
                return rule[:i], rule[i][:-1], rule[i+1:]
        return None, None, None

    def wrap_split(self, larger, smaller):
        for i in range(len(smaller) + 1):
            front, back = smaller[:i], smaller[i:]
            if starts_with(larger, front) and ends_with(larger, back):
                return front, back
        return None, None

    def directed_split(self, direction, derivation):
        if direction == self.LEFT:
            return derivation[0], derivation[1:]
        elif direction == self.RIGHT:
            return derivation[-1], derivation[:-1]
        else:
            assert False, "Invalid direction"

    def directed_merge(self, direction, directed, base):
        if direction == self.LEFT:
            return (directed + base)
        elif direction == self.RIGHT:
            return (base + directed)
        else:
            assert False, "Invalid direction"

    def remove_repeat(self, direction, front, mid, back):
        if direction == self.LEFT:
            return (front[:-len(mid)], back) if ends_with(front, mid) else None
        elif direction == self.RIGHT:
            return (front, back[len(mid):]) if starts_with(back, mid) else None
        else:
            assert False, "Invalid direction"

    def add_nonterminal(self, name, derivations):
        self.nonterminals[name] = derivations

    def make_fresh_nonterminal(self, name, rhs):
        if rhs in self.dedup:
            return self.dedup[rhs], False
        nonterminal = '{0}_{1}'.format(name, self.fresh_id)
        self.dedup[rhs] = nonterminal
        self.fresh_id += 1
        return nonterminal, True


class NonparserPrefixExtractor(ANTLRv4ParserVisitor):
    def defaultResult(self):
        return ''

    def aggregateResult(self, aggregate, next_result):
        if next_result:
            return aggregate + ' ' + next_result
        else:
            return aggregate

    def visitPrequelConstruct(self, ctx:ANTLRv4Parser.PrequelConstructContext):
        return self.visitChildren(ctx) + '\n\n'

    def visitTerminal(self, node):
        if isinstance(node, ANTLRv4Parser.TerminalContext):
            return self.visitChildren(node)

        token = node.getSymbol()
        blacklist = [
            'DOC_COMMENT', 'BLOCK_COMMENT', 'LINE_COMMENT'
        ]
        if ANTLRv4Lexer.symbolicNames[token.type] in blacklist or token.type <= 0:
            return ''
        return node.getText()

    def visitLexerRuleSpec(self, ctx: ANTLRv4Parser.LexerRuleSpecContext):
        return self.visitChildren(ctx) + '\n\n'

    def visitLexerAtom(self, ctx:ANTLRv4Parser.LexerAtomContext):
        return get_tree_as_string(ctx)

    def visitParserRuleSpec(self, ctx: ANTLRv4Parser.ParserRuleSpecContext):
        pass


class ParserRuleExtractor(ANTLRv4ParserVisitor):
    def __init__(self, grammar):
        self.grammar = grammar
        self.last_rule = None
        self.subrule_count = 0

    def visitLexerRuleSpec(self, ctx: ANTLRv4Parser.LexerRuleSpecContext):
        # Skip exploring lexer rules any further.
        pass

    def visitParserRuleSpec(self, ctx: ANTLRv4Parser.ParserRuleSpecContext):
        # Extract the name and reset subrules before exploring deeper.
        name = str(ctx.RULE_REF())
        self.last_rule = name
        self.subrule_count = 0

        # Recurse into the subtree of this rule.
        rules = ctx.ruleBlock().accept(self)
        self.grammar.add_nonterminal(name, rules)

    def visitRuleAltList(self, ctx: ANTLRv4Parser.ParserRuleSpecContext):
        return tuple(x.accept(self) for x in ctx.labeledAlt())

    def visitLabeledAlt(self, ctx: ANTLRv4Parser.LabeledAltContext):
        return ctx.alternative().accept(self)

    def visitAlternative(self, ctx: ANTLRv4Parser.AlternativeContext):
        return tuple(symbol for element in ctx.element()
                            for symbol in (element.accept(self),) if symbol)

    def visitElement(self, ctx: ANTLRv4Parser.ElementContext):
        if ctx.actionBlock():
            assert False, "Action block unhandled"
        # Get the base regardless of labeledElement, atom, or ebnf
        base = ctx.children[0].accept(self)
        if ctx.ebnfSuffix():
            return self.handleSuffix(ctx.ebnfSuffix(), base)
        else:
            return base

    def visitEbnf(self, ctx: ANTLRv4Parser.EbnfContext):
        base = ctx.block().accept(self)
        if ctx.blockSuffix():
            return self.handleSuffix(ctx.blockSuffix().ebnfSuffix(), base)
        else:
            return base

    def visitBlock(self, ctx: ANTLRv4Parser.BlockContext):
        rules = tuple(x.accept(self) for x in ctx.altList().alternative())
        self.subrule_count += 1
        name = '{0}_block_{1}'.format(self.last_rule, self.subrule_count)
        self.grammar.add_nonterminal(name, rules)
        return name

    def visitLabeledElement(self, ctx: ANTLRv4Parser.LabeledElementContext):
        to_extract = ctx.atom() or ctx.block()
        return to_extract.accept(self)

    def visitAtom(self, ctx: ANTLRv4Parser.AtomContext):
        if ctx.terminal():
            node = ctx.terminal().STRING_LITERAL() or ctx.terminal().TOKEN_REF()
            return str(node)
        elif ctx.ruleref():
            return str(ctx.ruleref().RULE_REF())
        elif ctx.notSet():
            return get_tree_as_string(ctx.notSet())
        elif ctx.characterRange():
            return get_tree_as_string(ctx.characterRange())
        else:
            return None

    def _handle_suffix_by_expanding(self, suffix, base):
        # TODO: These could be deduplicated across subrules with more work.
        self.subrule_count += 1
        name = '{0}_suffix_{1}'.format(self.last_rule, self.subrule_count)
        if suffix.STAR():
            rules = ((base, name), ())
        elif suffix.PLUS():
            rules = ((base, name), (base,))
        else:  # QUESTION
            rules = ((base,), ())
        self.grammar.add_nonterminal(name, rules)
        return name

    def _handle_suffix_directly(self, suffix, base):
        if suffix.STAR():
            return base + '*'
        elif suffix.PLUS():
            return base + '+'
        else:  # QUESTION
            return base + '?'

    handleSuffix = _handle_suffix_by_expanding


def make_builder(grammar_path, canonicalize_lexer_rules=True):
    input = FileStream(grammar_path)
    lexer = ANTLRv4Lexer(input)
    stream = CommonTokenStream(lexer)
    parser = ANTLRv4Parser(stream)
    tree = parser.grammarSpec()

    prefix = tree.accept(NonparserPrefixExtractor())
    builder = GrammarBuilder()
    parser_rule_extractor = ParserRuleExtractor(builder)
    tree.accept(parser_rule_extractor)
    return prefix, builder


def print_pnf_grammar(grammar_path, start):
    prefix, builder = make_builder(grammar_path)
    builder.to_pnf(start)
    as_str = builder.to_antlr_string()
    print(prefix, '\n', as_str)


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument("grammar", help="Path to an ANTLR4 grammar")
    parser.add_argument("start", help="Name of the start symbol in the grammar")
    args = parser.parse_args()

    print_pnf_grammar(args.grammar, args.start)
