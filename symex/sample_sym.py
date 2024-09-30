# User inputs:
a = sym()
b = sym()
c = sym()

# Program:
x = 3
y = 0
z = 0

if a > 0:
  x = -2

if b < 5:
  if (a == 0) and c > 0:
    y = 1
  z = 2

assert((x + y + z) != 3)
