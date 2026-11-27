import parsimony.composition_link_examples

namespace parsimony

section general

variable {vertex_count original_count part_count : ℕ} {domain_size : Fin original_count → ℕ}

theorem original_with_two_values_of_two_tuples (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (two_tuples : 2 ≤ relation_count csp originals) :
    ∃ x, originals x = true ∧ 2 ≤ csp.domain_size x := by
  by_contra none
  push Not at none
  have single : ∀ first second : original_tuple csp originals, first = second := by
    intro first second
    funext x
    apply Fin.ext
    have first_lt := (first x).isLt
    have second_lt := (second x).isLt
    have below := none x.val x.property
    omega
  have at_most_one : relation_count csp originals ≤ 1 := by
    unfold relation_count
    rw [Fintype.card_le_one_iff]
    intro first second
    exact Subtype.ext (single first.val second.val)
  omega

theorem hidden_with_two_values_of_not_parsimonious (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (not_parsimonious :
      ¬ is_parsimonious csp originals (minimal_support_encoding csp originals order)) :
    ∃ h, originals h = false ∧ 2 ≤ csp.domain_size h := by
  by_contra none
  push Not at none
  apply not_parsimonious
  apply minimal_support_parsimonious_of_singleton_hidden_domains csp originals order tree_order
    root_original
  intro h hidden
  have positive := csp.domain_nonempty h
  have below := none h hidden
  omega

theorem conjunction_minimal_support_part_sizes
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) (nonparsimonious_part : Fin part_count)
    (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x))
    (nonparsimonious_part_is : parts nonparsimonious_part = minimal_support_part csp originals order embed domain_match)
    (not_parsimonious :
      ¬ is_parsimonious csp originals (minimal_support_encoding csp originals order))
    (conjunction_parsimonious : model_count (conjunction_formula (linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card)
    (satisfiable : ∃ tuple, satisfies_all_parts (linked_problem parts) tuple) :
    3 ≤ vertex_count ∧ (∃ x, originals x = true ∧ 2 ≤ csp.domain_size x) ∧
      ∃ h, originals h = false ∧ 2 ≤ csp.domain_size h := by
  have part_not_parsimonious :
      ¬ is_parsimonious (parts nonparsimonious_part).csp (parts nonparsimonious_part).originals (parts nonparsimonious_part).formula := by
    rw [nonparsimonious_part_is]
    exact not_parsimonious
  have two_tuples := part_has_two_tuples_of_parsimonious_conjunction parts covers exact nonparsimonious_part part_not_parsimonious
    conjunction_parsimonious satisfiable
  rw [nonparsimonious_part_is] at two_tuples
  obtain ⟨x, x_original, x_two⟩ :=
    original_with_two_values_of_two_tuples csp originals two_tuples
  obtain ⟨h, h_hidden, h_two⟩ := hidden_with_two_values_of_not_parsimonious csp originals order
    tree_order root_original not_parsimonious
  refine ⟨?_, ⟨x, x_original, x_two⟩, ⟨h, h_hidden, h_two⟩⟩
  have values_differ : x.val ≠ h.val := by
    intro same
    have same_vertex : x = h := Fin.ext same
    rw [same_vertex, h_hidden] at x_original
    exact Bool.false_ne_true x_original
  have x_lt := x.isLt
  have h_lt := h.isLt
  by_contra small
  have exactly_two : vertex_count = 2 := by omega
  subst exactly_two
  exact conjunction_not_parsimonious_of_two_vertex_minimal_support_part parts covers exact nonparsimonious_part csp originals order
    tree_order root_original embed domain_match nonparsimonious_part_is not_parsimonious satisfiable
    conjunction_parsimonious

theorem conjunction_minimal_support_part_minimum
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) (nonparsimonious_part : Fin part_count)
    (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x))
    (nonparsimonious_part_is : parts nonparsimonious_part = minimal_support_part csp originals order embed domain_match)
    (not_parsimonious :
      ¬ is_parsimonious csp originals (minimal_support_encoding csp originals order))
    (conjunction_parsimonious : model_count (conjunction_formula (linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card)
    (satisfiable : ∃ tuple, satisfies_all_parts (linked_problem parts) tuple) :
    ∃ t x h : Fin vertex_count, t ≠ x ∧ t ≠ h ∧ x ≠ h ∧ originals x = true ∧
      originals h = false ∧ 1 ≤ csp.domain_size t ∧ 2 ≤ csp.domain_size x ∧
      2 ≤ csp.domain_size h := by
  obtain ⟨three, ⟨x, x_original, x_two⟩, ⟨h, h_hidden, h_two⟩⟩ :=
    conjunction_minimal_support_part_sizes parts covers exact nonparsimonious_part csp originals order tree_order
      root_original embed domain_match nonparsimonious_part_is not_parsimonious conjunction_parsimonious satisfiable
  have x_ne_h : x ≠ h := by
    intro same
    rw [same, h_hidden] at x_original
    exact Bool.false_ne_true x_original
  obtain ⟨t, t_ne_x, t_ne_h⟩ : ∃ t : Fin vertex_count, t ≠ x ∧ t ≠ h := by
    by_contra none
    push Not at none
    have covered : (Finset.univ : Finset (Fin vertex_count)) ⊆ {x, h} := by
      intro t _
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases t_x : t = x
      · exact Or.inl t_x
      · exact Or.inr (none t t_x)
    have card_bound := Finset.card_le_card covered
    rw [Finset.card_univ, Fintype.card_fin] at card_bound
    have pair_bound : ({x, h} : Finset (Fin vertex_count)).card ≤ 2 := Finset.card_le_two
    omega
  have t_positive := csp.domain_nonempty t
  exact ⟨t, x, h, t_ne_x, t_ne_h, x_ne_h, x_original, h_hidden, t_positive, x_two, h_two⟩

theorem conjunction_minimal_support_part_size_sum
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) (nonparsimonious_part : Fin part_count)
    (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x))
    (nonparsimonious_part_is : parts nonparsimonious_part = minimal_support_part csp originals order embed domain_match)
    (not_parsimonious :
      ¬ is_parsimonious csp originals (minimal_support_encoding csp originals order))
    (conjunction_parsimonious : model_count (conjunction_formula (linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card)
    (satisfiable : ∃ tuple, satisfies_all_parts (linked_problem parts) tuple) :
    5 ≤ ∑ v, csp.domain_size v := by
  obtain ⟨t, x, h, t_ne_x, t_ne_h, x_ne_h, -, -, t_one, x_two, h_two⟩ :=
    conjunction_minimal_support_part_minimum parts covers exact nonparsimonious_part csp originals order tree_order
      root_original embed domain_match nonparsimonious_part_is not_parsimonious conjunction_parsimonious satisfiable
  have triple_sum : ∑ v ∈ ({x, h, t} : Finset (Fin vertex_count)), csp.domain_size v =
      csp.domain_size x + csp.domain_size h + csp.domain_size t := by
    rw [Finset.sum_insert (by simp [x_ne_h, Ne.symm t_ne_x]), Finset.sum_pair (Ne.symm t_ne_h)]
    omega
  have subset_sum := Finset.sum_le_sum_of_subset (f := csp.domain_size)
    (Finset.subset_univ ({x, h, t} : Finset (Fin vertex_count)))
  omega

end general

namespace counterexamples

theorem ms_composition_attains_minimum :
    ms_part_csp.domain_size 0 = 1 ∧ ms_part_csp.domain_size 1 = 2 ∧
      ms_part_csp.domain_size 2 = 2 ∧ ∑ v, ms_part_csp.domain_size v = 5 ∧
      (middle_vertex_is_hidden : Fin 3 → Bool) 0 = true ∧
      (middle_vertex_is_hidden : Fin 3 → Bool) 1 = false ∧
      (middle_vertex_is_hidden : Fin 3 → Bool) 2 = true := by
  decide +kernel

theorem ms_composition_meets_minimum :
    3 ≤ 3 ∧ (∃ x, middle_vertex_is_hidden x = true ∧ 2 ≤ ms_part_csp.domain_size x) ∧
      ∃ h, middle_vertex_is_hidden h = false ∧ 2 ≤ ms_part_csp.domain_size h := by
  have not_parsimonious : ¬ is_parsimonious ms_part_csp middle_vertex_is_hidden
      (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2]) := by
    unfold is_parsimonious
    rw [ms_part_counts.2.2.2.1, ms_part_counts.2.1]
    decide
  have satisfiable : ∃ tuple, satisfies_all_parts (linked_problem ms_composition_parts) tuple := by
    have positive :
        0 < (Finset.univ.filter (satisfies_all_parts (linked_problem ms_composition_parts))).card := by
      rw [ms_composition_counts.1]
      decide
    obtain ⟨tuple, member⟩ := Finset.card_pos.mp positive
    exact ⟨tuple, (Finset.mem_filter.mp member).2⟩
  exact conjunction_minimal_support_part_sizes ms_composition_parts ms_composition_covers
    ms_composition_exact 0 ms_part_csp middle_vertex_is_hidden [0, 1, 2] ms_part_counts.1
    (by decide +kernel) ms_embed ms_domain_match rfl not_parsimonious
    (ms_composition_counts.2.trans ms_composition_counts.1.symm) satisfiable

end counterexamples

end parsimony
