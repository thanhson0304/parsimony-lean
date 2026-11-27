import parsimony.tree_order

namespace parsimony
namespace cp2022_examples

def example_six_relation (x y a b : ℕ) : Bool :=
  match x, y with
  | 0, 2 => decide (a + 1 + (b + 1) ≤ 5)
  | 2, 3 => a + 1 == 3 || b + 1 == 3
  | 1, 3 => decide (a + 1 + (b + 1) ≤ 5)
  | _, _ => false

def example_six_edge (x y : ℕ) : Bool :=
  (x == 0 && y == 2) || (x == 2 && y == 3) || (x == 1 && y == 3)

def example_six : binary_csp 4 where
  domain_size := fun _ => 3
  domain_nonempty := by decide
  adjacent := fun x y => example_six_edge x y || example_six_edge y x
  adjacent_symm := by decide +kernel
  adjacent_irrefl := by decide +kernel
  allowed := fun x y a b => example_six_relation x y a b || example_six_relation y x b a
  allowed_symm := by decide +kernel

def direct_value (x : Fin 4) (a : Fin 3) (polarity : Bool) :
    cnf_literal (boolean_variable example_six all_vertices) :=
  value_literal example_six all_vertices x a polarity

def direct_ladder (x : Fin 4) (i : Fin 2) (polarity : Bool) :
    cnf_literal (boolean_variable example_six all_vertices) :=
  ladder_literal example_six all_vertices ⟨x, rfl⟩ i polarity

def example_seven_clauses : cnf_formula (boolean_variable example_six all_vertices) :=
  (List.finRange 4).flatMap (fun x =>
    [[direct_value x 0 false, direct_ladder x 0 false],
      [direct_value x 0 true, direct_ladder x 0 true],
      [direct_value x 2 true, direct_ladder x 1 false],
      [direct_value x 2 false, direct_ladder x 1 true],
      [direct_ladder x 0 true, direct_ladder x 1 false],
      [direct_value x 1 true, direct_ladder x 1 true, direct_ladder x 0 false],
      [direct_value x 1 false, direct_ladder x 1 false],
      [direct_value x 1 false, direct_ladder x 0 true]]) ++
  [[direct_value 0 2 false, direct_value 2 2 false],
    [direct_value 1 2 false, direct_value 3 2 false],
    [direct_value 2 0 false, direct_value 3 1 false],
    [direct_value 2 0 false, direct_value 3 0 false],
    [direct_value 2 1 false, direct_value 3 0 false],
    [direct_value 2 1 false, direct_value 3 1 false]]

theorem example_seven_variable_count :
    Fintype.card (boolean_variable example_six all_vertices) = 20 := by
  decide +kernel

theorem example_seven_clauses_match :
    formula_as_sets (direct_encoding example_six) = formula_as_sets example_seven_clauses := by
  decide +kernel

theorem example_seven_clause_count :
    (formula_as_sets (direct_encoding example_six)).card = 38 := by
  decide +kernel

theorem bit_count_three : bit_count 3 = 2 := by
  decide +kernel

def log_bit (x : Fin 4) (position : Fin 2) (polarity : Bool) :
    cnf_literal (log_variable example_six) :=
  ((⟨x, position.cast bit_count_three.symm⟩ : log_variable example_six), polarity)

def example_six_clauses : cnf_formula (log_variable example_six) :=
  [[log_bit 0 0 false, log_bit 0 1 false],
    [log_bit 1 0 false, log_bit 1 1 false],
    [log_bit 2 0 false, log_bit 2 1 false],
    [log_bit 3 0 false, log_bit 3 1 false],
    [log_bit 0 0 false, log_bit 0 1 true, log_bit 2 0 false, log_bit 2 1 true],
    [log_bit 1 0 false, log_bit 1 1 true, log_bit 3 0 false, log_bit 3 1 true],
    [log_bit 2 0 true, log_bit 2 1 true, log_bit 3 0 true, log_bit 3 1 true],
    [log_bit 2 0 true, log_bit 2 1 false, log_bit 3 0 true, log_bit 3 1 true],
    [log_bit 2 0 true, log_bit 2 1 true, log_bit 3 0 true, log_bit 3 1 false],
    [log_bit 2 0 true, log_bit 2 1 false, log_bit 3 0 true, log_bit 3 1 false]]

theorem example_six_variable_count : Fintype.card (log_variable example_six) = 8 := by
  decide +kernel

theorem example_six_clauses_match :
    formula_as_sets (log_encoding example_six) = formula_as_sets example_six_clauses := by
  decide +kernel

theorem example_six_clause_count : (formula_as_sets (log_encoding example_six)).card = 10 := by
  decide +kernel

theorem source_tree_order_is_valid : is_tree_order example_six [0, 2, 3, 1] := by
  decide +kernel

theorem example_six_is_a_tree : is_binary_constraint_tree example_six :=
  is_binary_constraint_tree_of_tree_order example_six [0, 2, 3, 1] source_tree_order_is_valid 0
    (by decide +kernel)

theorem source_order_with_gap_is_not_a_tree_order : ¬ is_tree_order example_six [0, 1, 2, 3] := by
  decide +kernel

end cp2022_examples
end parsimony

#print axioms parsimony.cp2022_examples.example_seven_clauses_match
#print axioms parsimony.cp2022_examples.example_six_clauses_match
