import parsimony.tree_order

namespace parsimony
namespace counterexamples

abbrev edge_list := List (ℕ × ℕ × List (ℕ × ℕ))

def adjacent_of_edges {vertex_count : ℕ} (edges : edge_list) (x y : Fin vertex_count) : Bool :=
  edges.any fun edge =>
    (edge.1 == x.val && edge.2.1 == y.val) || (edge.1 == y.val && edge.2.1 == x.val)

def allowed_of_edges {vertex_count : ℕ} (edges : edge_list) (x y : Fin vertex_count) (a b : ℕ) :
    Bool :=
  edges.any fun edge =>
    (edge.1 == x.val && edge.2.1 == y.val && edge.2.2.contains (a, b)) ||
      (edge.1 == y.val && edge.2.1 == x.val && edge.2.2.contains (b, a))

def csp_of_edges (vertex_count : ℕ) (sizes : List ℕ) (edges : edge_list)
    (nonempty : ∀ x : Fin vertex_count, 0 < sizes.getD x.val 0)
    (irreflexive : ∀ x : Fin vertex_count, adjacent_of_edges edges x x = false) :
    binary_csp vertex_count where
  domain_size := fun x => sizes.getD x.val 0
  domain_nonempty := nonempty
  adjacent := adjacent_of_edges edges
  adjacent_symm := fun x y => by
    unfold adjacent_of_edges
    congr 1
    funext edge
    exact Bool.or_comm _ _
  adjacent_irrefl := irreflexive
  allowed := allowed_of_edges edges
  allowed_symm := fun x y a b => by
    unfold allowed_of_edges
    congr 1
    funext edge
    exact Bool.or_comm _ _

abbrev first_vertex_is_original {vertex_count : ℕ} : Fin vertex_count → Bool :=
  fun x => x.val == 0

abbrev middle_vertex_is_hidden {vertex_count : ℕ} : Fin vertex_count → Bool :=
  fun x => x.val != 1

abbrev second_vertex_is_original {vertex_count : ℕ} : Fin vertex_count → Bool :=
  fun x => x.val == 1

def copy_csp : binary_csp 2 :=
  csp_of_edges 2 [2, 2] [(0, 1, [(0, 0), (1, 1)])] (by decide) (by decide)

theorem copy_order_is_valid : is_tree_order copy_csp [0, 1] := by decide +kernel

theorem copy_is_a_tree : is_binary_constraint_tree copy_csp :=
  is_binary_constraint_tree_of_tree_order copy_csp [0, 1] copy_order_is_valid 0 (by decide +kernel)

def copy_value (x : Fin 2) (a : Fin (copy_csp.domain_size x)) (polarity : Bool) :
    cnf_literal (boolean_variable copy_csp first_vertex_is_original) :=
  value_literal copy_csp first_vertex_is_original x a polarity

def copy_ladder (polarity : Bool) :
    cnf_literal (boolean_variable copy_csp first_vertex_is_original) :=
  ladder_literal copy_csp first_vertex_is_original ⟨0, by decide⟩ ⟨0, by decide +kernel⟩ polarity

theorem copy_minimal_support_clauses :
    formula_as_sets (minimal_support_encoding copy_csp first_vertex_is_original [0, 1]) =
      formula_as_sets
        [[copy_value 0 ⟨0, by decide⟩ false, copy_ladder false],
          [copy_value 0 ⟨0, by decide⟩ true, copy_ladder true],
          [copy_value 0 ⟨1, by decide⟩ true, copy_ladder false],
          [copy_value 0 ⟨1, by decide⟩ false, copy_ladder true],
          [copy_value 0 ⟨0, by decide⟩ false, copy_value 1 ⟨0, by decide⟩ true],
          [copy_value 0 ⟨1, by decide⟩ false, copy_value 1 ⟨1, by decide⟩ true]] := by
  decide +kernel

theorem copy_root_is_original : root_is_original (first_vertex_is_original : Fin 2 → Bool) [0, 1] := by
  decide +kernel

theorem copy_relation_count : relation_count copy_csp first_vertex_is_original = 2 := by
  decide +kernel

theorem copy_has_unique_extension : has_unique_extension copy_csp first_vertex_is_original := by
  decide +kernel

theorem copy_minimal_support_models :
    model_count (minimal_support_encoding copy_csp first_vertex_is_original [0, 1]) = 4 := by
  decide +kernel

theorem copy_partial_support_models :
    model_count (partial_support_encoding copy_csp first_vertex_is_original) = 2 := by
  decide +kernel

theorem copy_support_models : model_count (support_encoding copy_csp) = 2 := by
  decide +kernel

theorem copy_direct_models : model_count (direct_encoding copy_csp) = 2 := by
  decide +kernel

theorem copy_min_eo_models : model_count (min_eo_encoding copy_csp [0, 1]) = 2 := by
  decide +kernel

theorem copy_minimal_support_is_not_parsimonious :
    ¬ is_parsimonious copy_csp first_vertex_is_original
      (minimal_support_encoding copy_csp first_vertex_is_original [0, 1]) := by
  rw [is_parsimonious, copy_minimal_support_models, copy_relation_count]
  decide

def smallest_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 2] [(0, 1, [(0, 0)])] (by decide) (by decide)

def smallest_value (x : Fin 2) (a : Fin (smallest_csp.domain_size x)) (polarity : Bool) :
    cnf_literal (boolean_variable smallest_csp first_vertex_is_original) :=
  value_literal smallest_csp first_vertex_is_original x a polarity

theorem smallest_order_is_valid : is_tree_order smallest_csp [0, 1] := by decide +kernel

theorem smallest_is_a_tree : is_binary_constraint_tree smallest_csp :=
  is_binary_constraint_tree_of_tree_order smallest_csp [0, 1] smallest_order_is_valid 0
    (by decide +kernel)

theorem smallest_relation_count : relation_count smallest_csp first_vertex_is_original = 1 := by
  decide +kernel

theorem smallest_minimal_support_clauses :
    formula_as_sets (minimal_support_encoding smallest_csp first_vertex_is_original [0, 1]) =
      formula_as_sets
        [[smallest_value 0 ⟨0, by decide⟩ true],
          [smallest_value 0 ⟨0, by decide⟩ false, smallest_value 1 ⟨0, by decide⟩ true]] := by
  decide +kernel

theorem smallest_minimal_support_models :
    model_count (minimal_support_encoding smallest_csp first_vertex_is_original [0, 1]) = 2 := by
  decide +kernel

theorem smallest_partial_support_models :
    model_count (partial_support_encoding smallest_csp first_vertex_is_original) = 1 := by
  decide +kernel

theorem smallest_minimal_support_is_not_parsimonious :
    ¬ is_parsimonious smallest_csp first_vertex_is_original
      (minimal_support_encoding smallest_csp first_vertex_is_original [0, 1]) := by
  rw [is_parsimonious, smallest_minimal_support_models, smallest_relation_count]
  decide

def dtbe_csp : binary_csp 4 :=
  csp_of_edges 4 [2, 1, 1, 2]
    [(0, 3, [(0, 0), (1, 1)]), (1, 3, [(0, 0), (0, 1)]), (2, 3, [(0, 0), (0, 1)])]
    (by decide) (by decide)

theorem dtbe_order_is_valid : is_tree_order dtbe_csp [0, 3, 1, 2] := by decide +kernel

theorem dtbe_is_a_tree : is_binary_constraint_tree dtbe_csp :=
  is_binary_constraint_tree_of_tree_order dtbe_csp [0, 3, 1, 2] dtbe_order_is_valid 0
    (by decide +kernel)

def dtbe_value (x : Fin 4) (a : Fin (dtbe_csp.domain_size x)) (polarity : Bool) :
    cnf_literal (boolean_variable dtbe_csp first_vertex_is_original) :=
  value_literal dtbe_csp first_vertex_is_original x a polarity

def dtbe_ladder (polarity : Bool) :
    cnf_literal (boolean_variable dtbe_csp first_vertex_is_original) :=
  ladder_literal dtbe_csp first_vertex_is_original ⟨0, by decide⟩ ⟨0, by decide +kernel⟩ polarity

theorem dtbe_minimal_support_clauses :
    formula_as_sets (minimal_support_encoding dtbe_csp first_vertex_is_original [0, 3, 1, 2]) =
      formula_as_sets
        [[dtbe_value 0 ⟨0, by decide⟩ false, dtbe_ladder false],
          [dtbe_value 0 ⟨0, by decide⟩ true, dtbe_ladder true],
          [dtbe_value 0 ⟨1, by decide⟩ true, dtbe_ladder false],
          [dtbe_value 0 ⟨1, by decide⟩ false, dtbe_ladder true],
          [dtbe_value 0 ⟨0, by decide⟩ false, dtbe_value 3 ⟨0, by decide⟩ true],
          [dtbe_value 0 ⟨1, by decide⟩ false, dtbe_value 3 ⟨1, by decide⟩ true],
          [dtbe_value 3 ⟨0, by decide⟩ false, dtbe_value 1 ⟨0, by decide⟩ true],
          [dtbe_value 3 ⟨1, by decide⟩ false, dtbe_value 1 ⟨0, by decide⟩ true],
          [dtbe_value 3 ⟨0, by decide⟩ false, dtbe_value 2 ⟨0, by decide⟩ true],
          [dtbe_value 3 ⟨1, by decide⟩ false, dtbe_value 2 ⟨0, by decide⟩ true]] := by
  decide +kernel

theorem dtbe_two_models_per_tuple :
    ∀ tuple, in_relation dtbe_csp first_vertex_is_original tuple →
      models_over_tuple dtbe_csp first_vertex_is_original first_vertex_is_original
        (minimal_support_encoding dtbe_csp first_vertex_is_original [0, 3, 1, 2]) tuple = 2 := by
  decide +kernel

theorem dtbe_relation_count : relation_count dtbe_csp first_vertex_is_original = 2 := by
  decide +kernel

theorem dtbe_has_unique_extension : has_unique_extension dtbe_csp first_vertex_is_original := by
  decide +kernel

theorem dtbe_minimal_support_models :
    model_count (minimal_support_encoding dtbe_csp first_vertex_is_original [0, 3, 1, 2]) = 4 := by
  decide +kernel

theorem dtbe_minimal_support_is_not_parsimonious :
    ¬ is_parsimonious dtbe_csp first_vertex_is_original
      (minimal_support_encoding dtbe_csp first_vertex_is_original [0, 3, 1, 2]) := by
  rw [is_parsimonious, dtbe_minimal_support_models, dtbe_relation_count]
  decide

def root_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 1] [(0, 1, [(0, 0)]), (1, 2, [(0, 0), (1, 0)])] (by decide) (by decide)

theorem root_first_order_is_valid : is_tree_order root_csp [0, 1, 2] := by decide +kernel

theorem root_is_a_tree : is_binary_constraint_tree root_csp :=
  is_binary_constraint_tree_of_tree_order root_csp [0, 1, 2] root_first_order_is_valid 0
    (by decide +kernel)

theorem root_last_order_is_valid : is_tree_order root_csp [2, 1, 0] := by decide +kernel

theorem root_relation_count : relation_count root_csp middle_vertex_is_hidden = 1 := by
  decide +kernel

theorem root_first_minimal_support_models :
    model_count (minimal_support_encoding root_csp middle_vertex_is_hidden [0, 1, 2]) = 2 := by
  decide +kernel

theorem root_last_minimal_support_models :
    model_count (minimal_support_encoding root_csp middle_vertex_is_hidden [2, 1, 0]) = 1 := by
  decide +kernel

def supported_root_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 1] [(0, 1, [(0, 0), (1, 1)]), (1, 2, [(0, 0), (1, 0)])]
    (by decide) (by decide)

theorem supported_root_first_order_is_valid : is_tree_order supported_root_csp [0, 1, 2] := by
  decide +kernel

theorem supported_root_is_a_tree : is_binary_constraint_tree supported_root_csp :=
  is_binary_constraint_tree_of_tree_order supported_root_csp [0, 1, 2]
    supported_root_first_order_is_valid 0 (by decide +kernel)

theorem supported_root_last_order_is_valid : is_tree_order supported_root_csp [2, 1, 0] := by
  decide +kernel

theorem supported_root_first_minimal_support_models :
    model_count (minimal_support_encoding supported_root_csp middle_vertex_is_hidden [0, 1, 2]) =
      4 := by
  decide +kernel

theorem supported_root_last_minimal_support_models :
    model_count (minimal_support_encoding supported_root_csp middle_vertex_is_hidden [2, 1, 0]) =
      2 := by
  decide +kernel

def two_extensions_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 2] [(0, 1, [(0, 0), (0, 1)])] (by decide) (by decide)

theorem two_extensions_relation_count :
    relation_count two_extensions_csp first_vertex_is_original = 1 := by
  decide +kernel

theorem two_extensions_support_models : model_count (support_encoding two_extensions_csp) = 2 := by
  decide +kernel

theorem two_extensions_partial_support_models :
    model_count (partial_support_encoding two_extensions_csp first_vertex_is_original) = 3 := by
  decide +kernel

def hidden_root_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 1] [(0, 1, [])] (by decide) (by decide)

theorem hidden_root_order_is_valid : is_tree_order hidden_root_csp [0, 1] := by decide +kernel

theorem hidden_root_is_not_original :
    ¬ root_is_original (second_vertex_is_original : Fin 2 → Bool) [0, 1] := by
  decide +kernel

theorem hidden_root_relation_count :
    relation_count hidden_root_csp second_vertex_is_original = 0 := by
  decide +kernel

theorem hidden_root_minimal_support_models :
    model_count (minimal_support_encoding hidden_root_csp second_vertex_is_original [0, 1]) = 1 := by
  decide +kernel

def inconsistent_path_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 1] [(0, 1, [(0, 0)]), (1, 2, [(1, 0)])] (by decide) (by decide)

theorem inconsistent_path_order_is_not_a_tree_order :
    ¬ is_tree_order inconsistent_path_csp [0, 2, 1] := by
  decide +kernel

theorem inconsistent_path_relation_count :
    relation_count inconsistent_path_csp middle_vertex_is_hidden = 0 := by
  decide +kernel

theorem inconsistent_path_minimal_support_models :
    model_count (minimal_support_encoding inconsistent_path_csp middle_vertex_is_hidden [0, 2, 1]) =
      1 := by
  decide +kernel

end counterexamples
end parsimony

#print axioms parsimony.counterexamples.copy_minimal_support_is_not_parsimonious
#print axioms parsimony.counterexamples.smallest_minimal_support_is_not_parsimonious
#print axioms parsimony.counterexamples.dtbe_minimal_support_is_not_parsimonious
#print axioms parsimony.counterexamples.root_first_minimal_support_models
#print axioms parsimony.counterexamples.root_last_minimal_support_models
