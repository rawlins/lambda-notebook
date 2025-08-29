import sys, re, traceback, collections, enum

from lamb.parsing import find_pattern_locations, consume_pattern, consume_whitespace
from lamb.parsing import consume_char, ParseError, struc_strip, flatten_paren_struc


def parsing_ts():
    from lamb.meta import get_type_system
    return get_type_system()


term_symbols_re = r'[a-zA-Z0-9]'
base_term_re = fr'{term_symbols_re}+'
full_term_re = fr'(_?{base_term_re})(_)?'
match_term_re = fr'{base_term_re}$'


def valid_op_symbol(s):
    from lamb.meta.core import is_op_symbol
    return is_op_symbol(s) or re.match(match_term_re, s) is not None


def find_term_locations(s, i=0):
    """Find locations in a string `s` that are term names."""
    # TODO: code dup with parse_term
    term_re = re.compile(full_term_re)
    unfiltered_result = find_pattern_locations(term_re, s, i=i, end=None)
    result = list()
    for r in unfiltered_result:
        if r.start() > 0 and s[r.start() - 1] == ".":
            # result is prefaced by a ".", and therefore is a functional
            # call or attribute
            continue
        result.append(r)
    return result


def parse_term(s, i=0, return_obj=True, assignment=None):
    """Parse position `i` in `s` as a term expression.  A term expression
    is some alphanumeric sequence followed optionally by an underscore and
    a type.  If a type is not specified locally, but is present in 
    `assignment`, use that.  If a type is specified and is present in
    `assignment`, check type compatibility immediately."""

    term_name, next = consume_pattern(s, i, full_term_re, return_match=True)

    if not term_name:
        if return_obj:
            return (None, i)
        else:
            return (None, None, i)

    if term_name.group(2):
        # try to parse a type
        # if there is a _, will force an attempt
        typ, end = parsing_ts().type_parser_recursive(s, next)
    else:
        typ = None
        end = next

    if return_obj:
        from lamb.meta import TypedExpr
        term = TypedExpr.term_factory(term_name.group(1), typ=typ,
                                assignment=assignment, preparsed=True)
        return (term, end)
    else:
        return (term_name.group(1), typ, end)


def try_parse_term_sequence(s, lower_bound=1, upper_bound=None,
                                                    assignment=None):
    """Try to parse `s` as a sequence of terms separated by commas. This
    consumes the entire string."""
    if not isinstance(s, str):
        s = struc_strip(s)
        if len(s) > 1:
            raise ParseError(f"Unparsable extraneous material in term sequence",
                s=flatten_paren_struc(s), i=0,
                met_preconditions=True)
        s = s[0]
        if not isinstance(s, str):
            s = debracket(s)
            if len(s) == 0:
                s = ""
            elif len(s) == 1:
                s = s[0]
            else:
                raise ParseError(f"Unparsable extraneous material in term sequence",
                    s=flatten_paren_struc(s), i=0,
                    met_preconditions=True)

            if not isinstance(s, str):
                raise ParseError(f"Extraneous parentheses in term sequence",
                    s=flatten_paren_struc(s), i=0,
                    met_preconditions=True)
    s = s.strip()
    if len(s) == 0:
        sequence = list()
        i = 0
    else:
        v, typ, i = parse_term(s, i=0, return_obj=False,
                                                    assignment=assignment)
        sequence = [(v, typ)]
    if i < len(s):
        i = consume_whitespace(s, i)
        if i < len(s) and v is None:
            raise ParseError(f"Extraneous character at beginning of term sequence (`{s[i]}`)",
                s=s, i=i, met_preconditions=True)
        while i < len(s):
            i = consume_char(s, i, ",", f"expected comma in variable sequence, found `{s[i]}`")
            i = consume_whitespace(s, i)
            v, typ, i = parse_term(s, i=i, return_obj=False,
                                                    assignment=assignment)
            if v is None:
                raise ParseError(
                    "Failed to find term following comma in variable sequence",
                    s=s, i=i, met_preconditions=True)
            sequence.append((v, typ))

    if lower_bound and len(sequence) < lower_bound:
        if lower_bound == 1 and upper_bound == 1:
            err = "Expected a variable"
        else:
            err = f"Too few variables ({len(sequence)} < {lower_bound}) in variable sequence"
        raise ParseError(err, s=s, i=i, met_preconditions=True)

    if upper_bound and len(sequence) > upper_bound:
        if upper_bound == 1:
            err = "Expected a single variable, got a sequence"
        else:
            err = f"Too many variables ({len(sequence)} > {upper_bound}) in variable sequence"
        raise ParseError(err, s=s, i=i, met_preconditions=True)
    return sequence


def try_parse_typed_term(s, assignment=None):
    """Try to parse string 's' as a typed term.
    assignment: a variable assignment to parse s with.

    Format: n_t
      * 'n': a term name.
        - initial numeric: term is a number.
        - initial alphabetic: term is a variable or constant.  (Variable:
          lowercase initial.)
      * 't': a type, optional.  If absent, will either get it from
        assignment, or return None as the 2nd element.

    Returns a tuple of a variable name, and a type.  If you want a
    TypedTerm, call one of the factory functions.

    Raises: TypeMismatch if the assignment supplies a type inconsistent
    with the specified one.
    """

    seq = try_parse_term_sequence(s, lower_bound=1, upper_bound=1,
                                                    assignment=assignment)
    return seq[0]
