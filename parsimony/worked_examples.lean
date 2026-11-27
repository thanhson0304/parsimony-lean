import parsimony.counterexamples
import parsimony.minimal_support
import parsimony.partial_support

namespace parsimony
namespace worked_examples

open counterexamples

def chain_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 2] [(0, 1, [(0, 0), (1, 1)]), (1, 2, [(0, 0), (1, 1)])]
    (by decide) (by decide)

theorem chain_order_is_valid : is_tree_order chain_csp [0, 1, 2] := by decide +kernel

theorem chain_root_is_original :
    root_is_original (middle_vertex_is_hidden : Fin 3 → Bool) [0, 1, 2] := by
  decide +kernel

theorem chain_relation_count : relation_count chain_csp middle_vertex_is_hidden = 2 := by
  decide +kernel

theorem chain_minimal_support_models :
    model_count (minimal_support_encoding chain_csp middle_vertex_is_hidden [0, 1, 2]) = 2 := by
  decide +kernel

theorem chain_minimal_support_is_parsimonious :
    is_parsimonious chain_csp middle_vertex_is_hidden
      (minimal_support_encoding chain_csp middle_vertex_is_hidden [0, 1, 2]) := by
  rw [is_parsimonious, chain_minimal_support_models, chain_relation_count]

theorem chain_upward_sets_are_singletons :
    ∀ tuple, in_relation chain_csp middle_vertex_is_hidden tuple →
      ∀ h, middle_vertex_is_hidden h = false →
        ∃! a, in_upward_set chain_csp middle_vertex_is_hidden [0, 1, 2] tuple h a :=
  (minimal_support_parsimonious_iff chain_csp middle_vertex_is_hidden [0, 1, 2]
    chain_order_is_valid chain_root_is_original).mp chain_minimal_support_is_parsimonious

theorem copy_upward_set_is_whole_domain (tuple : original_tuple copy_csp first_vertex_is_original)
    (a : Fin (copy_csp.domain_size 1)) :
    in_upward_set copy_csp first_vertex_is_original [0, 1] tuple 1 a := by
  refine (in_upward_set_iff copy_csp first_vertex_is_original [0, 1] tuple 1 a).mpr ⟨?_, ?_⟩
  · intro on_h
    exact absurd on_h (by decide)
  · intro y adjacent_h_y h_earlier
    exfalso
    revert y
    decide +kernel

theorem copy_upward_set_values_differ :
    (⟨0, by decide⟩ : Fin (copy_csp.domain_size 1)) ≠ ⟨1, by decide⟩ := by
  decide +kernel

theorem copy_general_theorem_agrees_with_count :
    ¬ is_parsimonious copy_csp first_vertex_is_original
      (minimal_support_encoding copy_csp first_vertex_is_original [0, 1]) := by
  intro parsimonious
  have singletons := (minimal_support_parsimonious_iff copy_csp first_vertex_is_original [0, 1]
    copy_order_is_valid copy_root_is_original).mp parsimonious
  have tuple_relation : in_relation copy_csp first_vertex_is_original
      (restrict_to_originals copy_csp first_vertex_is_original
        (fun x => ⟨0, copy_csp.domain_nonempty x⟩)) :=
    ⟨fun x => ⟨0, copy_csp.domain_nonempty x⟩, by decide +kernel, rfl⟩
  have unique_value := singletons _ tuple_relation 1 (by decide)
  exact copy_upward_set_values_differ (unique_value.unique
    (copy_upward_set_is_whole_domain _ _) (copy_upward_set_is_whole_domain _ _))

theorem copy_partial_support_is_parsimonious :
    is_parsimonious copy_csp first_vertex_is_original
      (partial_support_encoding copy_csp first_vertex_is_original) :=
  (partial_support_parsimonious_iff copy_csp first_vertex_is_original copy_is_a_tree
    ⟨0, by decide⟩).mpr copy_has_unique_extension

theorem copy_partial_support_count_agrees :
    model_count (partial_support_encoding copy_csp first_vertex_is_original) =
      relation_count copy_csp first_vertex_is_original :=
  copy_partial_support_is_parsimonious

theorem copy_support_is_parsimonious :
    is_parsimonious copy_csp first_vertex_is_original (support_encoding copy_csp) :=
  (support_parsimonious_iff copy_csp first_vertex_is_original).mpr copy_has_unique_extension

theorem copy_direct_is_parsimonious :
    is_parsimonious copy_csp first_vertex_is_original (direct_encoding copy_csp) :=
  (direct_parsimonious_iff copy_csp first_vertex_is_original).mpr copy_has_unique_extension

theorem copy_min_eo_is_parsimonious :
    is_parsimonious copy_csp first_vertex_is_original (min_eo_encoding copy_csp [0, 1]) :=
  (min_eo_parsimonious_iff copy_csp first_vertex_is_original [0, 1] copy_order_is_valid).mpr
    copy_has_unique_extension

theorem copy_solution_count :
    Fintype.card {candidate : assignment copy_csp // is_solution copy_csp candidate} = 2 := by
  decide +kernel

theorem copy_support_general_count :
    model_count (support_encoding copy_csp) = 2 :=
  (support_model_count copy_csp).trans copy_solution_count

theorem two_extensions_order_is_valid : is_tree_order two_extensions_csp [0, 1] := by
  decide +kernel

theorem two_extensions_is_a_tree : is_binary_constraint_tree two_extensions_csp :=
  is_binary_constraint_tree_of_tree_order two_extensions_csp [0, 1] two_extensions_order_is_valid 0
    (by decide +kernel)

theorem two_extensions_has_no_unique_extension :
    ¬ has_unique_extension two_extensions_csp first_vertex_is_original := by
  decide +kernel

theorem two_extensions_partial_support_is_not_parsimonious :
    ¬ is_parsimonious two_extensions_csp first_vertex_is_original
      (partial_support_encoding two_extensions_csp first_vertex_is_original) := fun parsimonious =>
  two_extensions_has_no_unique_extension
    ((partial_support_parsimonious_iff two_extensions_csp first_vertex_is_original
      two_extensions_is_a_tree ⟨0, by decide⟩).mp parsimonious)

theorem two_extensions_tuple_extension_count :
    ∀ tuple, in_relation two_extensions_csp first_vertex_is_original tuple →
      extension_count two_extensions_csp first_vertex_is_original tuple = 2 := by
  decide +kernel

theorem two_extensions_more_partial_support_models :
    ∀ tuple, in_relation two_extensions_csp first_vertex_is_original tuple →
      2 < models_over_tuple two_extensions_csp first_vertex_is_original first_vertex_is_original
        (partial_support_encoding two_extensions_csp first_vertex_is_original) tuple := by
  intro tuple tuple_relation
  have count_is_two := two_extensions_tuple_extension_count tuple tuple_relation
  have more := more_partial_support_models_than_extensions two_extensions_csp
    first_vertex_is_original two_extensions_is_a_tree ⟨0, by decide⟩ tuple (by omega)
  omega

abbrev no_vertex_is_original {vertex_count : ℕ} : Fin vertex_count → Bool := fun _ => false

def no_original_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 1] [(0, 1, [])] (by decide) (by decide)

theorem no_original_relation_count : relation_count no_original_csp no_vertex_is_original = 0 := by
  decide +kernel

theorem no_original_partial_support_models :
    model_count (partial_support_encoding no_original_csp no_vertex_is_original) = 1 := by
  decide +kernel

end worked_examples
end parsimony
