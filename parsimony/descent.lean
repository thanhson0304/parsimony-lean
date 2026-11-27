import parsimony.semantics

namespace parsimony

variable {vertex_count : ℕ}

theorem index_zero_of_head (order : List (Fin vertex_count)) (root : Fin vertex_count)
    (head_is_root : order.head? = some root) : order.idxOf root = 0 := by
  cases order with
  | nil => simp at head_is_root
  | cons first rest =>
    have first_is_root : first = root := by simpa using head_is_root
    subst first_is_root
    simp

theorem exists_solution_by_descent (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
    (family : ∀ x, Fin (csp.domain_size x) → Prop)
    (root : Fin vertex_count) (root_first : order.idxOf root = 0)
    (root_value : Fin (csp.domain_size root)) (root_in_family : family root root_value)
    (children : ∀ x y, csp.adjacent x y = true → earlier_in order x y = true →
      ∀ a, family x a → ∃ b : Fin (csp.domain_size y),
        csp.allowed x y a b = true ∧ family y b) :
    ∃ candidate : assignment csp, candidate root = root_value ∧
      (∀ x, family x (candidate x)) ∧ is_solution csp candidate := by
  classical
  have position_bound : ∀ x, order.idxOf x < order.length :=
    fun x => List.idxOf_lt_length_iff.mpr (tree_order.2.1 x)
  have up_to_reached : ∀ reached, ∃ candidate : assignment csp, candidate root = root_value ∧
      ∀ x, order.idxOf x < reached → family x (candidate x) ∧
        ∀ earlier, csp.adjacent earlier x = true → order.idxOf earlier < order.idxOf x →
          csp.allowed earlier x (candidate earlier) (candidate x) = true := by
    intro reached
    induction reached with
    | zero =>
      refine ⟨Function.update (fun x => ⟨0, csp.domain_nonempty x⟩) root root_value, by simp, ?_⟩
      intro x below_zero
      omega
    | succ reached previous =>
      obtain ⟨candidate, candidate_root, candidate_prefix⟩ := previous
      by_cases in_range : reached < order.length
      · let next_vertex := order[reached]
        have next_position : order.idxOf next_vertex = reached :=
          List.Nodup.idxOf_getElem tree_order.1 reached in_range
        by_cases at_start : reached = 0
        · refine ⟨candidate, candidate_root, ?_⟩
          intro x x_position
          have x_is_root : x = root := by
            by_contra x_ne_root
            exact tree_order_positions_differ csp order tree_order x root x_ne_root (by omega)
          subst x_is_root
          refine ⟨by rw [candidate_root]; exact root_in_family, ?_⟩
          intro earlier _ earlier_position
          omega
        · obtain ⟨parent, parent_adjacent, parent_earlier, parent_unique⟩ :=
            tree_order_unique_earlier_neighbour csp order tree_order next_vertex (by omega)
          have parent_fact := candidate_prefix parent (by omega)
          obtain ⟨next_value, next_allowed, next_in_family⟩ :=
            children parent next_vertex parent_adjacent (by simpa [earlier_in] using parent_earlier)
              (candidate parent) parent_fact.1
          have ne_of_position : ∀ x, order.idxOf x < reached → x ≠ next_vertex := by
            intro x x_position x_is_next
            rw [x_is_next] at x_position
            omega
          have root_ne_next : root ≠ next_vertex := ne_of_position root (by omega)
          refine ⟨Function.update candidate next_vertex next_value, ?_, ?_⟩
          · rw [Function.update_of_ne root_ne_next]
            exact candidate_root
          · intro x x_position
            by_cases x_is_next : x = next_vertex
            · subst x_is_next
              rw [Function.update_self]
              refine ⟨next_in_family, ?_⟩
              intro earlier earlier_adjacent earlier_position
              have earlier_is_parent := parent_unique earlier earlier_adjacent earlier_position
              subst earlier_is_parent
              rw [Function.update_of_ne (ne_of_position earlier (by omega))]
              exact next_allowed
            · have x_below : order.idxOf x < reached := by
                have differ := tree_order_positions_differ csp order tree_order x next_vertex
                  x_is_next
                omega
              have x_fact := candidate_prefix x x_below
              rw [Function.update_of_ne x_is_next]
              refine ⟨x_fact.1, ?_⟩
              intro earlier earlier_adjacent earlier_position
              rw [Function.update_of_ne (ne_of_position earlier (by omega))]
              exact x_fact.2 earlier earlier_adjacent earlier_position
      · refine ⟨candidate, candidate_root, ?_⟩
        intro x x_position
        exact candidate_prefix x (by have := position_bound x; omega)
  obtain ⟨candidate, candidate_root, candidate_all⟩ := up_to_reached order.length
  refine ⟨candidate, candidate_root, fun x => (candidate_all x (position_bound x)).1, ?_⟩
  intro x y adjacent_x_y
  have x_ne_y : x ≠ y := by
    intro x_is_y
    subst x_is_y
    rw [csp.adjacent_irrefl] at adjacent_x_y
    exact absurd adjacent_x_y (by decide)
  have differ := tree_order_positions_differ csp order tree_order x y x_ne_y
  rcases Nat.lt_or_gt_of_ne differ with x_earlier | y_earlier
  · exact (candidate_all y (position_bound y)).2 x adjacent_x_y x_earlier
  · rw [csp.allowed_symm x y]
    have adjacent_y_x : csp.adjacent y x = true := by
      rw [csp.adjacent_symm]
      exact adjacent_x_y
    exact (candidate_all x (position_bound x)).2 y adjacent_y_x y_earlier

end parsimony
