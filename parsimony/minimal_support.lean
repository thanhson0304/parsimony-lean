import parsimony.descent

namespace parsimony

variable {vertex_count : ℕ}

theorem minimal_support_model_has_supported_solution (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (minimal_support_encoding csp originals order)) :
    ∃ candidate : assignment csp, is_solution csp candidate ∧
      ∀ x, valuation (Sum.inl ⟨x, candidate x⟩) = true := by
  obtain ⟨blocks, edges⟩ := (is_model_minimal_support_iff csp originals order valuation).mp model
  obtain ⟨root, head_is_root, root_on⟩ := root_original
  obtain ⟨root_value, root_fixed⟩ := blocks root root_on
  obtain ⟨candidate, _, all_selected, solution⟩ := exists_solution_by_descent csp order tree_order
    (fun x a => valuation (Sum.inl ⟨x, a⟩) = true) root (index_zero_of_head order root head_is_root)
    root_value (by simp [root_fixed.1 root_value])
    (fun x y adjacent_x_y x_earlier a a_selected => edges x y adjacent_x_y x_earlier a a_selected)
  exact ⟨candidate, solution, all_selected⟩

theorem minimal_support_activation (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (minimal_support_encoding csp originals order))
    (x : Fin vertex_count) : ∃ a, valuation (Sum.inl ⟨x, a⟩) = true := by
  obtain ⟨candidate, _, all_selected⟩ := minimal_support_model_has_supported_solution csp originals
    order tree_order root_original valuation model
  exact ⟨candidate x, all_selected x⟩

theorem valuation_of_solution_is_minimal_support_model (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (candidate : assignment csp) (solution : is_solution csp candidate) :
    is_model (valuation_of_assignment csp originals candidate)
      (minimal_support_encoding csp originals order) :=
  (is_model_minimal_support_iff csp originals order _).mpr
    ⟨fun x on_x => ⟨candidate x, valuation_of_assignment_block csp originals candidate x on_x⟩,
      fun x y adjacent_x_y _ =>
        valuation_of_solution_edge csp originals candidate solution x y adjacent_x_y⟩

theorem minimal_support_is_projection_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order) :
    is_projection_exact csp originals originals (minimal_support_encoding csp originals order) := by
  constructor
  · intro valuation model
    obtain ⟨blocks, _⟩ := (is_model_minimal_support_iff csp originals order valuation).mp model
    choose tuple tuple_fixed using fun x : original_vertex originals => blocks x.val x.property
    obtain ⟨candidate, solution, all_selected⟩ := minimal_support_model_has_supported_solution csp
      originals order tree_order root_original valuation model
    refine ⟨tuple, ⟨candidate, solution, ?_⟩, fun x a => (tuple_fixed x).1 a⟩
    funext x
    have selected := all_selected x.val
    rw [(tuple_fixed x).1 (candidate x.val)] at selected
    exact of_decide_eq_true selected
  · rintro tuple ⟨candidate, solution, restricted⟩
    subst restricted
    exact ⟨valuation_of_assignment csp originals candidate,
      valuation_of_solution_is_minimal_support_model csp originals order candidate solution,
      valuation_of_assignment_encodes csp originals originals candidate⟩

theorem in_upward_set_iff (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)
    (x : Fin vertex_count) (a : Fin (csp.domain_size x)) :
    in_upward_set csp originals order tuple x a ↔
      (∀ on_x : originals x = true, a = tuple ⟨x, on_x⟩) ∧
        ∀ y, csp.adjacent x y = true → earlier_in order x y = true →
          ∃ b : Fin (csp.domain_size y), csp.allowed x y a b = true ∧
            in_upward_set csp originals order tuple y b := by
  constructor
  · rintro (⟨_, _, fits_tuple, witness, witness_allowed, witness_in_set⟩)
    exact ⟨fits_tuple, fun y adjacent_x_y x_earlier =>
      ⟨witness y adjacent_x_y x_earlier, witness_allowed y adjacent_x_y x_earlier,
        witness_in_set y adjacent_x_y x_earlier⟩⟩
  · rintro ⟨fits_tuple, has_witness⟩
    choose witness witness_allowed witness_in_set using has_witness
    exact in_upward_set.intro x a fits_tuple witness witness_allowed witness_in_set

theorem position_gap_decreases (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (x y : Fin vertex_count)
    (x_earlier : earlier_in order x y = true) :
    order.length - order.idxOf y < order.length - order.idxOf x := by
  have y_bound : order.idxOf y < order.length := List.idxOf_lt_length_iff.mpr (tree_order.2.1 y)
  have below : order.idxOf x < order.idxOf y := by simpa [earlier_in] using x_earlier
  omega

theorem selected_in_upward_set (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (tuple : original_tuple csp originals)
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (minimal_support_encoding csp originals order))
    (over_tuple : encodes_tuple csp originals originals valuation tuple) :
    ∀ x a, valuation (Sum.inl ⟨x, a⟩) = true → in_upward_set csp originals order tuple x a := by
  obtain ⟨_, edges⟩ := (is_model_minimal_support_iff csp originals order valuation).mp model
  have by_gap : ∀ gap x, order.length - order.idxOf x = gap → ∀ a,
      valuation (Sum.inl ⟨x, a⟩) = true → in_upward_set csp originals order tuple x a := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | _ gap inductive_case =>
      intro x x_gap a a_selected
      refine (in_upward_set_iff csp originals order tuple x a).mpr ⟨?_, ?_⟩
      · intro on_x
        have fixed := over_tuple ⟨x, on_x⟩ a
        rw [a_selected] at fixed
        exact of_decide_eq_true fixed.symm
      · intro y adjacent_x_y x_earlier
        obtain ⟨b, b_allowed, b_selected⟩ := edges x y adjacent_x_y x_earlier a a_selected
        exact ⟨b, b_allowed, inductive_case (order.length - order.idxOf y)
          (by rw [← x_gap]; exact position_gap_decreases csp order tree_order x y x_earlier)
          y rfl b b_selected⟩
  exact fun x a a_selected => by_gap _ x rfl a a_selected

theorem extension_in_upward_set (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (candidate : assignment csp)
    (solution : is_solution csp candidate) :
    ∀ x, in_upward_set csp originals order (restrict_to_originals csp originals candidate) x
      (candidate x) := by
  have by_gap : ∀ gap x, order.length - order.idxOf x = gap →
      in_upward_set csp originals order (restrict_to_originals csp originals candidate) x
        (candidate x) := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | _ gap inductive_case =>
      intro x x_gap
      refine (in_upward_set_iff csp originals order _ x (candidate x)).mpr
        ⟨fun _ => rfl, ?_⟩
      intro y adjacent_x_y x_earlier
      exact ⟨candidate y, solution x y adjacent_x_y,
        inductive_case (order.length - order.idxOf y)
          (by rw [← x_gap]; exact position_gap_decreases csp order tree_order x y x_earlier) y rfl⟩
  exact fun x => by_gap _ x rfl

open Classical in
noncomputable def valuation_of_upward_sets (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) : boolean_variable csp originals → Bool
  | Sum.inl pair => decide (in_upward_set csp originals order tuple pair.1 pair.2)
  | Sum.inr pair => decide (pair.2.val < (tuple pair.1).val)

theorem valuation_of_upward_sets_is_model (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (candidate : assignment csp)
    (solution : is_solution csp candidate) :
    is_model (valuation_of_upward_sets csp originals order
        (restrict_to_originals csp originals candidate))
      (minimal_support_encoding csp originals order) ∧
    encodes_tuple csp originals originals
      (valuation_of_upward_sets csp originals order
        (restrict_to_originals csp originals candidate))
      (restrict_to_originals csp originals candidate) := by
  classical
  have original_member_iff : ∀ x (on_x : originals x = true) (a : Fin (csp.domain_size x)),
      in_upward_set csp originals order (restrict_to_originals csp originals candidate) x a ↔
        a = candidate x := by
    intro x on_x a
    constructor
    · intro member
      exact ((in_upward_set_iff csp originals order _ x a).mp member).1 on_x
    · intro a_is_candidate
      rw [a_is_candidate]
      exact extension_in_upward_set csp originals order tree_order candidate solution x
  constructor
  · refine (is_model_minimal_support_iff csp originals order _).mpr ⟨?_, ?_⟩
    · intro x on_x
      refine ⟨candidate x, ?_, fun i => rfl⟩
      intro a
      exact decide_eq_decide.mpr (original_member_iff x on_x a)
    · intro x y adjacent_x_y x_earlier a a_selected
      have member : in_upward_set csp originals order
          (restrict_to_originals csp originals candidate) x a := by
        simpa [valuation_of_upward_sets] using a_selected
      obtain ⟨b, b_allowed, b_member⟩ :=
        ((in_upward_set_iff csp originals order _ x a).mp member).2 y adjacent_x_y x_earlier
      exact ⟨b, b_allowed, by simpa [valuation_of_upward_sets] using b_member⟩
  · intro x a
    exact decide_eq_decide.mpr (original_member_iff x.val x.property a)

theorem minimal_support_parsimonious_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order) :
    is_parsimonious csp originals (minimal_support_encoding csp originals order) ↔
      ∀ tuple, in_relation csp originals tuple →
        ∀ h, originals h = false → ∃! a, in_upward_set csp originals order tuple h a := by
  classical
  rw [is_parsimonious_iff_unique_models csp originals originals _
    (minimal_support_is_projection_exact csp originals order tree_order root_original)]
  constructor
  · rintro unique_models tuple ⟨candidate, solution, restricted⟩ h _
    subst restricted
    have singleton_model := valuation_of_solution_is_minimal_support_model csp originals order
      candidate solution
    have singleton_encodes := valuation_of_assignment_encodes csp originals originals candidate
    obtain ⟨upward_model, upward_encodes⟩ := valuation_of_upward_sets_is_model csp originals order
      tree_order candidate solution
    have same_valuation := (unique_models _ ⟨candidate, solution, rfl⟩).unique
      ⟨upward_model, upward_encodes⟩ ⟨singleton_model, singleton_encodes⟩
    refine ⟨candidate h, extension_in_upward_set csp originals order tree_order candidate solution h,
      ?_⟩
    intro a member
    have at_a := congrFun same_valuation (Sum.inl ⟨h, a⟩)
    have left_true : valuation_of_upward_sets csp originals order
        (restrict_to_originals csp originals candidate) (Sum.inl ⟨h, a⟩) = true := by
      simpa [valuation_of_upward_sets] using member
    rw [left_true] at at_a
    simpa [valuation_of_assignment] using at_a.symm
  · rintro hidden_unique tuple ⟨candidate, solution, restricted⟩
    subst restricted
    refine ⟨valuation_of_assignment csp originals candidate,
      ⟨valuation_of_solution_is_minimal_support_model csp originals order candidate solution,
        valuation_of_assignment_encodes csp originals originals candidate⟩, ?_⟩
    rintro other ⟨other_model, other_encodes⟩
    obtain ⟨blocks, _⟩ := (is_model_minimal_support_iff csp originals order other).mp other_model
    have hidden_selected_iff : ∀ x, originals x = false → ∀ a,
        other (Sum.inl ⟨x, a⟩) = true ↔ a = candidate x := by
      intro x x_hidden a
      have unique_at_x := hidden_unique _ ⟨candidate, solution, rfl⟩ x x_hidden
      have candidate_member := extension_in_upward_set csp originals order tree_order candidate
        solution x
      have selected_member := selected_in_upward_set csp originals order tree_order _ other
        other_model other_encodes x
      constructor
      · intro a_selected
        exact unique_at_x.unique (selected_member a a_selected) candidate_member
      · intro a_is_candidate
        obtain ⟨selected_value, value_selected⟩ := minimal_support_activation csp originals order
          tree_order root_original other other_model x
        have value_is_candidate := unique_at_x.unique (selected_member selected_value value_selected)
          candidate_member
        rw [a_is_candidate, ← value_is_candidate]
        exact value_selected
    funext variable_name
    rcases variable_name with ⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩
    · cases x_kind : originals x with
      | true =>
        exact other_encodes ⟨x, x_kind⟩ a
      | false =>
        have selected_iff := hidden_selected_iff x x_kind a
        show other (Sum.inl ⟨x, a⟩) = decide (a = candidate x)
        cases other_value : other (Sum.inl ⟨x, a⟩) with
        | true => simpa using (selected_iff.mp other_value).symm ▸ rfl
        | false =>
          have not_candidate : a ≠ candidate x := fun is_candidate => by
            have := selected_iff.mpr is_candidate
            rw [other_value] at this
            exact absurd this (by decide)
          simp [not_candidate]
    · obtain ⟨chosen, chosen_fixed⟩ := blocks x on_x
      have chosen_is_candidate : chosen = candidate x := by
        have at_chosen := chosen_fixed.1 chosen
        have self_true : decide (chosen = chosen) = true := by simp
        rw [other_encodes ⟨x, on_x⟩ chosen, self_true] at at_chosen
        exact of_decide_eq_true at_chosen
      show other (Sum.inr ⟨⟨x, on_x⟩, i⟩) = decide (i.val < (candidate x).val)
      rw [chosen_fixed.2 i, chosen_is_candidate]

end parsimony
