read "../DifferenceElimination.mpl":

vars := [
  x,
  y
];

eqs := [
  numer(x1 - (1 - b) * x0 / (x0 + a1_ * y0) - b * x0),
  numer(y1 - (1 - b) * y0 / (a2_ * x0 + y0) - b * y0),
  x0 + y0 - c
]:

B := ComputeBound(eqs, [x, y]):
print(cat("The bound is ", B));
elim_result := DifferenceElimination(eqs, vars, [x, y], {a1_, a2_, b, c}):
print("The result of elimination is ", elim_result);
