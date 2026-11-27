import parsimony.reduction_examples
import parsimony.minimal_support_counting

namespace parsimony

variable {vertex_count : ℕ}

def evaluated_size (csp : binary_csp vertex_count) : ℕ :=
  ∑ x : Fin vertex_count, ∑ y : Fin vertex_count,
    if csp.adjacent x y = true ∧ x < y then csp.domain_size x * csp.domain_size y else 0

theorem ct_start_old_evaluated_size : evaluated_size counterexamples.ct_start_old_csp = 15 := by
  decide +kernel

theorem ct_start_new_evaluated_size : evaluated_size counterexamples.ct_start_new_csp = 10 := by
  decide +kernel

theorem minimal_support_parsimonious_of_singleton_hidden_domains (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (singleton_hidden : ∀ h, originals h = false → csp.domain_size h = 1) :
    is_parsimonious csp originals (minimal_support_encoding csp originals order) := by
  rw [minimal_support_parsimonious_iff csp originals order tree_order root_original]
  intro tuple in_rel h h_hidden
  obtain ⟨candidate, solution, restricted⟩ := in_rel
  refine ⟨candidate h, ?_, ?_⟩
  · have upward := extension_in_upward_set csp originals order tree_order candidate solution h
    rw [restricted] at upward
    exact upward
  · intro b _
    apply Fin.ext
    have b_lt := b.isLt
    have candidate_lt := (candidate h).isLt
    have domain_one := singleton_hidden h h_hidden
    omega

theorem two_vertex_minimal_support_dichotomy (csp : binary_csp 2) (originals : Fin 2 → Bool)
    (order : List (Fin 2)) (tree_order : is_tree_order csp order)
    (root_original : root_is_original originals order) :
    is_parsimonious csp originals (minimal_support_encoding csp originals order) ∨
      ∀ tuple, in_relation csp originals tuple →
        2 ≤ models_over_tuple csp originals originals (minimal_support_encoding csp originals order)
          tuple := by
  by_cases all_singleton : ∀ h, originals h = false → csp.domain_size h = 1
  · exact Or.inl (minimal_support_parsimonious_of_singleton_hidden_domains csp originals order
      tree_order root_original all_singleton)
  · right
    push Not at all_singleton
    obtain ⟨h, h_hidden, h_not_one⟩ := all_singleton
    obtain ⟨root, root_head, root_is_original⟩ := root_original
    have root_first : order.idxOf root = 0 := index_zero_of_head order root root_head
    have h_ne_root : h ≠ root := by
      intro h_is_root
      rw [h_is_root, root_is_original] at h_hidden
      exact absurd h_hidden (by decide)
    have other_is_root : ∀ x : Fin 2, x ≠ h → x = root := by
      intro x x_ne_h
      apply Fin.ext
      have x_lt := x.isLt
      have h_lt := h.isLt
      have root_lt := root.isLt
      have x_ne := Fin.val_ne_of_ne x_ne_h
      have root_ne := Fin.val_ne_of_ne h_ne_root
      omega
    have only_hidden : ∀ x, originals x = false → x = h := by
      intro x x_hidden
      by_contra x_ne_h
      rw [other_is_root x x_ne_h, root_is_original] at x_hidden
      exact absurd x_hidden (by decide)
    have h_position : 0 < order.idxOf h := by
      have differ := tree_order_positions_differ csp order tree_order h root h_ne_root
      omega
    obtain ⟨parent, parent_adjacent, parent_lt, _⟩ :=
      tree_order_unique_earlier_neighbour csp order tree_order h h_position
    have parent_is_root : parent = root :=
      other_is_root parent (adjacent_ne csp parent h parent_adjacent)
    rw [parent_is_root] at parent_adjacent parent_lt
    have root_earlier : earlier_in order root h = true := by simpa [earlier_in] using parent_lt
    intro tuple in_rel
    rw [one_hidden_model_count csp originals order tree_order h root h_hidden only_hidden
      parent_adjacent root_earlier tuple in_rel]
    have upper_is_domain : (children_compatible_values csp originals order tuple h).card =
        csp.domain_size h := by
      have all_values : children_compatible_values csp originals order tuple h = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro b _ c adjacent_h_c h_earlier
        exfalso
        have c_is_root : c = root := other_is_root c (adjacent_ne csp h c adjacent_h_c).symm
        rw [c_is_root] at h_earlier
        have h_before : order.idxOf h < order.idxOf root := by simpa [earlier_in] using h_earlier
        omega
      rw [all_values, Finset.card_univ, Fintype.card_fin]
    have lower_count := parent_compatible_count_eq_extension_count csp originals order tree_order h
      root h_hidden only_hidden parent_adjacent root_earlier tuple in_rel
    have lower_positive : 0 < extension_count csp originals tuple := by
      obtain ⟨candidate, solution, restricted⟩ := in_rel
      exact Fintype.card_pos_iff.mpr ⟨⟨candidate, solution, restricted⟩⟩
    have lower_le_upper : (parent_compatible_values csp originals order tuple h root).card ≤
        (children_compatible_values csp originals order tuple h).card :=
      Finset.card_filter_le _ _
    have domain_large : 2 ≤ csp.domain_size h := by
      have positive := csp.domain_nonempty h
      omega
    rw [upper_is_domain] at lower_le_upper ⊢
    rw [lower_count] at lower_le_upper ⊢
    have smaller_power : 2 ^ (csp.domain_size h - extension_count csp originals tuple) ≤
        2 ^ (csp.domain_size h - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have split_power : 2 ^ csp.domain_size h = 2 * 2 ^ (csp.domain_size h - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have half_large : 2 ≤ 2 ^ (csp.domain_size h - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (csp.domain_size h - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end parsimony
