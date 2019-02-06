read "../DifferenceElimination.mpl":

vars := [
  A,
  B
];

eqs := [
  A1 - A0 * (2 * B0 - A0),
  B1 - A0^2 - B0^2
]:

bound := ComputeBound(eqs, [B]):
print(cat("The bound is ", bound));
elim_result := DifferenceElimination(eqs, vars, [B]):
print(cat("The result of elimination is ", elim_result));
