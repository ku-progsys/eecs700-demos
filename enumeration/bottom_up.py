from itertools import permutations, product

grammar = {
  'L': [['sort', 'L'],
        ['splice', 'L', 'N', 'N'],
        ['concat', 'L', 'L'],
        ['single', 'N'],
        ['x']],
  'N': [['find', 'L', 'N'],
        ['0']]
}

# CHANGE ME FOR DEPTH
max_depth = 4

def populate_cache(cache, non_term, d, new_term):
  # inserts things in the cache creating the right default values
  if non_term not in cache:
    cache[non_term] = {}
  if d not in cache[non_term]:
    cache[non_term][d] = []
  cache[non_term][d].append(new_term)

def new_terms(non_term, rule, cache, d):
  k = len(rule) - 1
  if d == 0 and k == 0:
    yield rule
  else:
    if k == 0:
      # doesn't show up in algorithm, because this is an artifact of the
      # implementation. Our implementation knows something is a non-terminal
      # only when it is a list with length > 1
      return

    # possible depth values for subterms
    d_choices = permutations(range(d), k)
    for d_choice in d_choices:
      # all the non-terminals to expand from the production rule
      non_terms_to_expand = rule[1:]
      # all the index tuples of cache to extract subterm
      cache_tuples = zip(non_terms_to_expand, d_choice)
      # all the extracted subterms
      subterm_choices = map(lambda ptr: cache.get(ptr[0]).get(ptr[1], []), cache_tuples)
      # choose one of each subterm from the cache
      subterms = product(*subterm_choices)
      for subterm in subterms:
        subterm = list(subterm)
        # make the subterm according to rule and return
        subterm.insert(0, rule[0])
        yield subterm

def bottom_up(grammar, examples):
  # we are ignoring examples for this demo
  cache = {} # called bank in the slides

  for d in range(max_depth):
    for non_term, rules in grammar.items():
      for rule in rules:
        for t in new_terms(non_term, rule, cache, d):
          # here we should test if t satisfies our input/output example
          # instead we are just printing the terms
          print(t)
          populate_cache(cache, non_term, d, t)

bottom_up(grammar, [])
