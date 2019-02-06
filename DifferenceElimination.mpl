# Implementation of algorithms based on the paper
# "Effective difference elimination and Nullstellensatz"
# by A. Ovchinnikov, G. Pogudin, and T. Scanlon
# https://arxiv.org/abs/1712.01412

  # Computes B(m, D) defined in the beginning of Section 3 the paper
  B := proc(dim, deg)
    local result;
    result := 0: 
    if dim = 0 then
      result := deg:
    end if:
    if dim = 1 then
      result := deg^3 / 6 + deg^2 / 2 + 4 * deg / 3 + 1;
    end if:
    if dim > 1 then
      result := B(dim - 1, deg) + deg^B(dim - 1, deg):
    end if:
    result:
  end proc:

  ComputeBound := proc(eqs, vars_to_eliminate) 
  local diff_vars_to_eliminate, m, d0, d1, h, i, j, ord, h_sum, ideal, 
  components, degrees, hpoly, dim, deg, result;
    h := GetOrdersForSystem(eqs, vars_to_eliminate):
    print(h);
    diff_vars_to_eliminate := {}:
    for i from 1 to nops(h) do
      for j from 0 to h[i] - 1 do
        diff_vars_to_eliminate := { op(diff_vars_to_eliminate), MakeShift(vars_to_eliminate[i], j) };
      end do:
    end do:
    m := Groebner[HilbertDimension](eqs, diff_vars_to_eliminate):

    ideal := PolynomialIdeals[PolynomialIdeal](eqs, variables = diff_vars_to_eliminate):
    components := [PolynomialIdeals[PrimeDecomposition](ideal)]:
    print("Num components ", nops(components));
    deg_total := 0:
    dim_max := 0:
    for i from 1 to nops(components) do
      hpoly := Groebner[HilbertPolynomial]( PolynomialIdeals[Generators](components[i]), tdeg(op(diff_vars_to_eliminate), aux_var), hilb_var ):
      dim := degree(hpoly, hilb_var):
      deg := coeff(hpoly, hilb_var, dim) * (dim)!:
      if hpoly <> 0 then
        deg_total := deg_total + deg:
        dim_max := max(dim_max, dim):
      end if:
    end do:
    print(deg_total, dim_max);
    B(dim_max, deg_total):
  end proc:

  # If number_prolongations = -1, then the algorithm tries all possible numbers form 1 to the bound
  # If number_prolongations => 0, then the algorithm performs the specified number of prolongations
  DifferenceElimination := proc(eqs, vars, vars_to_eliminate, parameters := {}, number_prolongations := -1) 
  local B, prolonged, h, i, ord, h_sum, vars_to_keep, result, diff_vars_to_eliminate, diff_vars_to_keep, eliminant;
    B := ComputeBound(eqs, vars_to_eliminate);
    prolonged := eqs;

    h := GetOrdersForSystem(eqs, vars):
    h_sum := foldl(`+`, op(h)):
    vars_to_keep := select(v -> not v in vars_to_eliminate, vars):
    result := []:

    for i from 1 to B do
      prolonged := [
        op(prolonged),
        seq( ShiftM(prolonged[-j], vars, i + h_sum), j = 1..nops(eqs) )
      ]:
      if number_prolongations <> -1 and number_prolongations <> i then
        next;
      end if:
      diff_vars_to_eliminate := select(
        v -> nops(DecomposeShift(v, vars_to_eliminate)) = 2,
        indets(prolonged)
      ):
      diff_vars_to_keep := select(
        v -> nops(DecomposeShift(v, vars_to_keep)) = 2,
        indets(prolonged)
      ):
      diff_vars_to_keep := {op(diff_vars_to_keep), op(parameters)}:
      print(diff_vars_to_keep);
      eliminant := PolynomialIdeals[EliminationIdeal](
        PolynomialIdeals[PolynomialIdeal](prolonged, variables = {op(diff_vars_to_eliminate), op(diff_vars_to_keep)}),
        diff_vars_to_keep
      ):
      print(eliminant);
      if PolynomialIdeals[Generators](eliminant) <> {} then
        print("Hi", eliminant, PolynomialIdeals[Generators](eliminant));
        result := PolynomialIdeals[Generators](eliminant):
        break:
      end if:
    end do:

    result:
  end proc:

########### Auxiliary procedures for working with difference polynomials ################
# General convention: variables are strings not ending with digits
# shifts of a variable v are of the form v0, v1, v2, ...

  MakeShift := proc(var_name, der_order):
    cat(var_name, der_order):
  end proc:

  ##########################################

  ShiftOnce := proc(diff_poly, var_list, max_ord) local shift_operator, v, j:
    shift_operator := {}:
    for v in var_list do
      for j from 0 to max_ord do
        shift_operator := {op(shift_operator), MakeShift(v, j) = MakeShift(v, j + 1)}:
      end do:
    end do:
    subs(shift_operator, diff_poly):
  end proc:

  ##########################################

  ShiftM := proc(diff_poly, var_list, max_ords, ord := 1) local result, i;
    result := diff_poly:
    for i from 1 to ord do
      result := ShiftOnce(result, var_list, max_ords):
    end do:
    result:
  end proc:

  ##########################################

  # decomposes a shift into [variable, order], if possible
  DecomposeShift := proc(diff_var, vars) local matched, var, v, ord;
    matched := false:
    var := 0:
    for v in vars do
      if StringTools[IsPrefix](v, diff_var) then
        matched := true:
        var := v:
      end if:
    end do:
    if matched = true then
      ord := parse(StringTools[Drop](diff_var, length(var))):
      [var, ord];
    else
      [];
    end if:
  end proc:

  #########################################

  GetOrders := proc(diff_poly, vars) 
  local result, diff_vars, i, diff_v, decomposition;
    result := [seq(-1, i = 0..nops(vars))];
    diff_vars := indets(diff_poly):
    for i from 1 to nops(vars) do
      for diff_v in diff_vars do
        decomposition := DecomposeShift(diff_v, [vars[i]]):
        if nops(decomposition) = 2 then
          result[i] := max(result[i], decomposition[2]):
        end if:
      end do:
    end do:
    return result;
  end proc:

  GetOrdersForSystem := proc(eqs, vars)
  local i, h, ord;
    h := [seq(-1, i = 1..nops(vars))]:
    for i from 1 to nops(eqs) do
      ord := GetOrders(eqs[i], vars):
      h := [seq(max(h[i], ord[i] + 1), i = 1..nops(vars))]:
    end do:
    h;
  end proc:

#####################################################################


