import parsimony.composition_link
import parsimony.composition_examples
import parsimony.size_and_minimality

namespace parsimony

section general

variable {original_count part_count : ℕ} {domain_size : Fin original_count → ℕ}

theorem linked_composition_not_parsimonious_of_doubled_part
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) (nonparsimonious_part : Fin part_count)
    (doubled : ∀ tuple, in_relation (parts nonparsimonious_part).csp (parts nonparsimonious_part).originals tuple →
      2 ≤ models_over_tuple (parts nonparsimonious_part).csp (parts nonparsimonious_part).originals (parts nonparsimonious_part).ladder_on
        (parts nonparsimonious_part).formula tuple)
    (satisfiable : ∃ tuple, satisfies_all_parts (linked_problem parts) tuple) :
    model_count (conjunction_formula (linked_problem parts)) ≠
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card := by
  intro parsimonious
  obtain ⟨tuple, satisfied⟩ := satisfiable
  have one := (linked_composition_parsimonious_iff parts covers exact).mp parsimonious tuple
    satisfied nonparsimonious_part
  have two := doubled (tuple_on_part (parts nonparsimonious_part) tuple)
    ((linked_satisfies_all_parts_iff parts tuple).mp satisfied nonparsimonious_part)
  rw [one] at two
  exact absurd two (by decide)

theorem conjunction_not_parsimonious_of_two_vertex_minimal_support_part
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) (nonparsimonious_part : Fin part_count)
    (csp : binary_csp 2) (originals : Fin 2 → Bool) (order : List (Fin 2))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x))
    (nonparsimonious_part_is : parts nonparsimonious_part = minimal_support_part csp originals order embed domain_match)
    (not_parsimonious :
      ¬ is_parsimonious csp originals (minimal_support_encoding csp originals order))
    (satisfiable : ∃ tuple, satisfies_all_parts (linked_problem parts) tuple) :
    model_count (conjunction_formula (linked_problem parts)) ≠
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card := by
  refine linked_composition_not_parsimonious_of_doubled_part parts covers exact nonparsimonious_part ?_ satisfiable
  rw [nonparsimonious_part_is]
  exact (two_vertex_minimal_support_dichotomy csp originals order tree_order
    root_original).resolve_left not_parsimonious

theorem part_has_two_tuples_of_parsimonious_conjunction (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) (part : Fin part_count)
    (not_parsimonious :
      ¬ is_parsimonious (parts part).csp (parts part).originals (parts part).formula)
    (conjunction_parsimonious : model_count (conjunction_formula (linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card)
    (satisfiable : ∃ tuple, satisfies_all_parts (linked_problem parts) tuple) :
    2 ≤ relation_count (parts part).csp (parts part).originals := by
  obtain ⟨tuple, satisfied⟩ := satisfiable
  have kept_one := (linked_composition_parsimonious_iff parts covers exact).mp
    conjunction_parsimonious tuple satisfied part
  have kept_in_rel := (linked_satisfies_all_parts_iff parts tuple).mp satisfied part
  have exists_other : ∃ other, in_relation (parts part).csp (parts part).originals other ∧
      models_over_tuple (parts part).csp (parts part).originals (parts part).ladder_on
        (parts part).formula other ≠ 1 := by
    by_contra no_other
    apply not_parsimonious
    rw [is_parsimonious_iff_unique_models _ _ _ _ (exact part).2]
    intro other other_in_rel
    refine (models_over_tuple_eq_one_iff _ _ _ _ other).mp ?_
    by_contra other_count
    exact no_other ⟨other, other_in_rel, other_count⟩
  obtain ⟨other, other_in_rel, other_count⟩ := exists_other
  have differ : (⟨tuple_on_part (parts part) tuple, kept_in_rel⟩ :
      {candidate : original_tuple (parts part).csp (parts part).originals //
        in_relation (parts part).csp (parts part).originals candidate}) ≠
      ⟨other, other_in_rel⟩ := by
    intro same
    apply other_count
    have same_tuple : tuple_on_part (parts part) tuple = other := congrArg Subtype.val same
    rw [← same_tuple]
    exact kept_one
  unfold relation_count
  exact Fintype.one_lt_card_iff.mpr ⟨_, _, differ⟩

theorem linked_models_agree_on_original_ladders
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part))
    (first second : global_variable (linked_problem parts) → Bool)
    (first_model : is_model first (conjunction_formula (linked_problem parts)))
    (second_model : is_model second (conjunction_formula (linked_problem parts)))
    (same_values : ∀ (original : Fin original_count) (value : Fin (domain_size original)),
      first (Sum.inl ⟨original, Sum.inl value⟩) = second (Sum.inl ⟨original, Sum.inl value⟩))
    (original : Fin original_count) (step : Fin (domain_size original - 1)) :
    first (Sum.inl ⟨original, Sum.inr step⟩) = second (Sum.inl ⟨original, Sum.inr step⟩) := by
  obtain ⟨first_tuple, _, first_encodes⟩ :=
    (linked_composition_projection_exact parts covers exact).1 first first_model
  obtain ⟨second_tuple, _, second_encodes⟩ :=
    (linked_composition_projection_exact parts covers exact).1 second second_model
  have first_bits := (linked_global_encodes_iff parts first first_tuple).mp first_encodes original
  have second_bits :=
    (linked_global_encodes_iff parts second second_tuple).mp second_encodes original
  have same_tuple : first_tuple original = second_tuple original := by
    have at_value := (first_bits.1 (first_tuple original)).symm.trans
      ((same_values original (first_tuple original)).trans
        (second_bits.1 (first_tuple original)))
    exact (decide_eq_decide.mp at_value).mp rfl
  refine (first_bits.2 step).trans (Eq.trans ?_ (second_bits.2 step).symm)
  rw [same_tuple]

end general

namespace counterexamples

def identity_embed : original_vertex (all_vertices : Fin 2 → Bool) → Fin 2 := fun x => x.val

def ms_sizes : Fin 2 → ℕ := ![1, 2]

def ms_embed : original_vertex (middle_vertex_is_hidden : Fin 3 → Bool) → Fin 2 :=
  fun x => if x.val = 0 then 0 else 1

def ms_restriction_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 2] [(0, 1, [(0, 0)])] (by decide) (by decide)

theorem ms_domain_match : ∀ x : original_vertex (middle_vertex_is_hidden : Fin 3 → Bool),
    ms_part_csp.domain_size x.val = ms_sizes (ms_embed x) := by
  decide +kernel

theorem ms_restriction_domain_match : ∀ x : original_vertex (all_vertices : Fin 2 → Bool),
    ms_restriction_csp.domain_size x.val = ms_sizes (identity_embed x) := by
  decide +kernel

def ms_composition_parts : Fin 2 → linked_part ms_sizes :=
  ![minimal_support_part ms_part_csp middle_vertex_is_hidden [0, 1, 2] ms_embed ms_domain_match,
    support_part ms_restriction_csp all_vertices identity_embed ms_restriction_domain_match]

theorem ms_composition_counts :
    (Finset.univ.filter (satisfies_all_parts (linked_problem ms_composition_parts))).card = 1 ∧
      model_count (conjunction_formula (linked_problem ms_composition_parts)) = 1 := by
  decide +kernel

theorem ms_composition_covers : covers_all_originals (linked_problem ms_composition_parts) := by
  unfold covers_all_originals
  decide +kernel

theorem ms_composition_exact : ∀ part, is_exact_part (ms_composition_parts part) := by
  intro part
  fin_cases part
  · exact minimal_support_part_is_exact ms_part_csp middle_vertex_is_hidden [0, 1, 2]
      ms_part_counts.1 (by decide +kernel) ms_embed ms_domain_match
  · exact support_part_is_exact ms_restriction_csp all_vertices identity_embed ms_restriction_domain_match

theorem ms_composition_every_part_has_one_model :
    ∀ tuple, satisfies_all_parts (linked_problem ms_composition_parts) tuple →
      ∀ part, models_over_tuple (ms_composition_parts part).csp
        (ms_composition_parts part).originals (ms_composition_parts part).ladder_on
        (ms_composition_parts part).formula (tuple_on_part (ms_composition_parts part) tuple) = 1 :=
  (linked_composition_parsimonious_iff ms_composition_parts ms_composition_covers
    ms_composition_exact).mp (ms_composition_counts.2.trans ms_composition_counts.1.symm)

def conjunction_sizes : Fin 2 → ℕ := ![2, 1]

def conjunction_embed : original_vertex (first_vertex_is_original : Fin 2 → Bool) → Fin 2 :=
  fun _ => 0

def conjunction_restriction_csp : binary_csp 2 :=
  csp_of_edges 2 [2, 1] [(0, 1, [(0, 0)])] (by decide) (by decide)

theorem conjunction_domain_match :
    ∀ x : original_vertex (first_vertex_is_original : Fin 2 → Bool),
      conjunction_part_csp.domain_size x.val = conjunction_sizes (conjunction_embed x) := by
  decide +kernel

theorem conjunction_restriction_domain_match : ∀ x : original_vertex (all_vertices : Fin 2 → Bool),
    conjunction_restriction_csp.domain_size x.val = conjunction_sizes (identity_embed x) := by
  decide +kernel

def conjunction_support_parts : Fin 2 → linked_part conjunction_sizes :=
  ![support_part conjunction_part_csp first_vertex_is_original conjunction_embed conjunction_domain_match,
    support_part conjunction_restriction_csp all_vertices identity_embed conjunction_restriction_domain_match]

def conjunction_direct_parts : Fin 2 → linked_part conjunction_sizes :=
  ![direct_part conjunction_part_csp first_vertex_is_original conjunction_embed conjunction_domain_match,
    direct_part conjunction_restriction_csp all_vertices identity_embed conjunction_restriction_domain_match]

def conjunction_min_eo_parts : Fin 2 → linked_part conjunction_sizes :=
  ![min_eo_part conjunction_part_csp first_vertex_is_original [0, 1] conjunction_embed
      conjunction_domain_match,
    min_eo_part conjunction_restriction_csp all_vertices [0, 1] identity_embed
      conjunction_restriction_domain_match]

def conjunction_partial_support_parts : Fin 2 → linked_part conjunction_sizes :=
  ![partial_support_part conjunction_part_csp first_vertex_is_original conjunction_embed
      conjunction_domain_match,
    partial_support_part conjunction_restriction_csp all_vertices identity_embed
      conjunction_restriction_domain_match]

theorem conjunction_support_composition :
    (Finset.univ.filter (satisfies_all_parts (linked_problem conjunction_support_parts))).card = 1 ∧
      model_count (conjunction_formula (linked_problem conjunction_support_parts)) = 1 := by
  decide +kernel

theorem conjunction_direct_composition :
    (Finset.univ.filter (satisfies_all_parts (linked_problem conjunction_direct_parts))).card = 1 ∧
      model_count (conjunction_formula (linked_problem conjunction_direct_parts)) = 1 := by
  decide +kernel

theorem conjunction_min_eo_composition :
    (Finset.univ.filter (satisfies_all_parts (linked_problem conjunction_min_eo_parts))).card = 1 ∧
      model_count (conjunction_formula (linked_problem conjunction_min_eo_parts)) = 1 := by
  decide +kernel

theorem conjunction_partial_support_composition :
    (Finset.univ.filter
        (satisfies_all_parts (linked_problem conjunction_partial_support_parts))).card = 1 ∧
      model_count (conjunction_formula (linked_problem conjunction_partial_support_parts)) = 1 := by
  decide +kernel

end counterexamples

end parsimony
