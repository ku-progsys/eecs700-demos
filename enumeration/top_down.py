from itertools import permutations, product
from copy import deepcopy

grammar = {
  'L': [['sort', 'L'],
        ['splice', 'L', 'N', 'N'],
        ['concat', 'L', 'L'],
        ['single', 'N'],
        'x'],
  'N': [['find', 'L', 'N'],
        '0']
}

# CHANGE ME FOR SIZE
max_size = 10

# test is a given program is complete, i.e., has no non-terminals
def complete(grammar, term):
  if type(term) == str:
    return term not in grammar.keys()
  elif type(term) == list:
    for tok in term:
      if not complete(grammar, tok):
        return False
  return True

# finds the first leftmost non-terminal in a given program
def left_non_terminal(grammar, term):
  if type(term) == str:
    if term in grammar.keys():
      return term
    else:
      return None
  elif type(term) == list:
    for tok in term:
      res = left_non_terminal(grammar, tok)
      if res is not None:
        return res

# given a program, it replaces a leftmost non-terminal with a production rule
def replace_left_non_terminal(term, non_term, prod):
  if type(term) == str and term == non_term:
    return deepcopy(prod)
  elif type(term) == str and term != non_term:
    return term
  elif type(term) == list:
    for i in range(len(term)):
      updated = replace_left_non_terminal(term[i], non_term, prod)
      if updated != term[i]:
        # non terminal has been replaced
        term[i] = updated
        break
    return term

# computes the size of a program
def size(term):
  if type(term) == str:
    return 1
  else:
    return sum(map(lambda t: size(t), term))

# unroll term to fill in all possible productions; see slides
def unroll(grammar, term):
  new_terms = []

  non_terminal = left_non_terminal(grammar, term)
  for prod_rule in grammar[non_terminal]:
    new_term = replace_left_non_terminal(deepcopy(term), non_terminal, prod_rule)
    if size(term) <= max_size:
      new_terms.append(new_term)
    
  return new_terms

# the top-down search routine; see slides
def top_down(grammar, examples):
  wl = ['L']
  while len(wl) != 0:
    term = wl.pop(0)
    if complete(grammar, term):
      # you can test the program here, we are just printing
      print(term)
    else:
      wl += unroll(grammar, term)

top_down(grammar, [])
