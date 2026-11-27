import parsimony.minimal_support_counting

namespace parsimony

variable {vertex_count : ℕ}

def is_rule_one_selection (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)
    (h parent : Fin vertex_count)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool) : Prop :=
  (∀ a, selected h a = false) ∧
  (∀ x (on_x : originals x = true) (a : Fin (csp.domain_size x)),
    selected x a = decide (a = tuple ⟨x, on_x⟩)) ∧
  (∀ x y, x ≠ h → y ≠ h → csp.adjacent x y = true → earlier_in order x y = true →
    ∀ a : Fin (csp.domain_size x), selected x a = true →
      ∃ b : Fin (csp.domain_size y), csp.allowed x y a b = true ∧ selected y b = true) ∧
  ∀ a : Fin (csp.domain_size parent), selected parent a = true →
    ∃ c : Fin (csp.domain_size h), csp.allowed parent h a c = true

def is_rule_two_selection (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)
    (h parent child : Fin vertex_count)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool) : Prop :=
  (∀ a, selected h a = false) ∧
  (∀ x (on_x : originals x = true) (a : Fin (csp.domain_size x)),
    selected x a = decide (a = tuple ⟨x, on_x⟩)) ∧
  (∀ x y, x ≠ h → y ≠ h → csp.adjacent x y = true → earlier_in order x y = true →
    ∀ a : Fin (csp.domain_size x), selected x a = true →
      ∃ b : Fin (csp.domain_size y), csp.allowed x y a b = true ∧ selected y b = true) ∧
  ∀ a : Fin (csp.domain_size parent), selected parent a = true →
    ∃ c : Fin (csp.domain_size child),
      (∃ b : Fin (csp.domain_size h), csp.allowed parent h a b = true ∧
        csp.allowed h child b c = true) ∧ selected child c = true

theorem not_earlier_both_ways (order : List (Fin vertex_count)) (x y : Fin vertex_count)
    (x_earlier : earlier_in order x y = true) (y_earlier : earlier_in order y x = true) : False := by
  simp only [earlier_in, decide_eq_true_eq] at x_earlier y_earlier
  omega

theorem rule_one_forget_is_selection (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h parent : Fin vertex_count)
    (h_hidden : originals h = false) (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (selection : is_selection_over csp originals order tuple selected) :
    is_rule_one_selection csp originals order tuple h parent
      (Function.update selected h fun _ => false) := by
  obtain ⟨fixed, supported⟩ := selection
  have parent_ne : parent ≠ h := adjacent_ne csp parent h parent_adjacent
  refine ⟨fun a => by rw [Function.update_self], ?_, ?_, ?_⟩
  · intro x on_x a
    have x_ne : x ≠ h := by
      intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    rw [Function.update_of_ne x_ne]
    exact fixed x on_x a
  · intro x y x_ne y_ne adjacent_x_y x_earlier a a_selected
    rw [Function.update_of_ne x_ne] at a_selected
    obtain ⟨b, allowed_b, b_selected⟩ := supported x y adjacent_x_y x_earlier a a_selected
    exact ⟨b, allowed_b, by rw [Function.update_of_ne y_ne]; exact b_selected⟩
  · intro a a_selected
    rw [Function.update_of_ne parent_ne] at a_selected
    obtain ⟨c, allowed_c, _⟩ := supported parent h parent_adjacent parent_earlier a a_selected
    exact ⟨c, allowed_c⟩

theorem rule_one_lift_is_selection (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h parent : Fin vertex_count)
    (h_hidden : originals h = false) (leaf : ∀ z, csp.adjacent h z = true → z = parent)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (reduced : is_rule_one_selection csp originals order tuple h parent selected) :
    is_selection_over csp originals order tuple (Function.update selected h fun _ => true) := by
  obtain ⟨_, fixed, supported, restricted⟩ := reduced
  have parent_ne : parent ≠ h := adjacent_ne csp parent h parent_adjacent
  constructor
  · intro x on_x a
    have x_ne : x ≠ h := by
      intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    rw [Function.update_of_ne x_ne]
    exact fixed x on_x a
  · intro x y adjacent_x_y x_earlier a a_selected
    by_cases x_is_h : x = h
    · subst x_is_h
      have y_is_parent := leaf y adjacent_x_y
      subst y_is_parent
      exact (not_earlier_both_ways order x y x_earlier parent_earlier).elim
    · rw [Function.update_of_ne x_is_h] at a_selected
      by_cases y_is_h : y = h
      · subst y_is_h
        have x_is_parent : x = parent := by
          apply leaf x
          rw [csp.adjacent_symm]
          exact adjacent_x_y
        subst x_is_parent
        obtain ⟨c, allowed_c⟩ := restricted a a_selected
        exact ⟨c, allowed_c, by rw [Function.update_self]⟩
      · obtain ⟨b, allowed_b, b_selected⟩ :=
          supported x y x_is_h y_is_h adjacent_x_y x_earlier a a_selected
        exact ⟨b, allowed_b, by rw [Function.update_of_ne y_is_h]; exact b_selected⟩

open Classical in
theorem rule_one_minimal_support_count_le (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h parent : Fin vertex_count)
    (h_hidden : originals h = false) (leaf : ∀ z, csp.adjacent h z = true → z = parent)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true) :
    Fintype.card {selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool //
        is_rule_one_selection csp originals order tuple h parent selected} ≤
      models_over_tuple csp originals originals (minimal_support_encoding csp originals order)
        tuple := by
  classical
  rw [minimal_support_models_over_tuple_eq_selection_count]
  refine Fintype.card_le_of_surjective
    (fun selection => ⟨Function.update selection.val h fun _ => false,
      rule_one_forget_is_selection csp originals order tuple h parent h_hidden parent_adjacent
        parent_earlier selection.val selection.property⟩) ?_
  rintro ⟨reduced, reduced_property⟩
  refine ⟨⟨Function.update reduced h fun _ => true,
    rule_one_lift_is_selection csp originals order tuple h parent h_hidden leaf parent_adjacent
      parent_earlier reduced reduced_property⟩, ?_⟩
  apply Subtype.ext
  show Function.update (Function.update reduced h fun _ => true) h (fun _ => false) = reduced
  rw [Function.update_idem]
  have at_h : reduced h = fun _ => false := funext reduced_property.1
  rw [← at_h, Function.update_eq_self]

theorem rule_two_forget_is_selection (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h parent child : Fin vertex_count)
    (h_hidden : originals h = false) (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (child_adjacent : csp.adjacent h child = true) (child_later : earlier_in order h child = true)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (selection : is_selection_over csp originals order tuple selected) :
    is_rule_two_selection csp originals order tuple h parent child
      (Function.update selected h fun _ => false) := by
  obtain ⟨fixed, supported⟩ := selection
  have parent_ne : parent ≠ h := adjacent_ne csp parent h parent_adjacent
  have child_ne : child ≠ h := fun child_is_h => adjacent_ne csp h child child_adjacent child_is_h.symm
  refine ⟨fun a => by rw [Function.update_self], ?_, ?_, ?_⟩
  · intro x on_x a
    have x_ne : x ≠ h := by
      intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    rw [Function.update_of_ne x_ne]
    exact fixed x on_x a
  · intro x y x_ne y_ne adjacent_x_y x_earlier a a_selected
    rw [Function.update_of_ne x_ne] at a_selected
    obtain ⟨b, allowed_b, b_selected⟩ := supported x y adjacent_x_y x_earlier a a_selected
    exact ⟨b, allowed_b, by rw [Function.update_of_ne y_ne]; exact b_selected⟩
  · intro a a_selected
    rw [Function.update_of_ne parent_ne] at a_selected
    obtain ⟨b, allowed_b, b_selected⟩ :=
      supported parent h parent_adjacent parent_earlier a a_selected
    obtain ⟨c, allowed_c, c_selected⟩ := supported h child child_adjacent child_later b b_selected
    exact ⟨c, ⟨b, allowed_b, allowed_c⟩, by rw [Function.update_of_ne child_ne]; exact c_selected⟩

theorem rule_two_lift_is_selection (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h parent child : Fin vertex_count)
    (h_hidden : originals h = false)
    (two_neighbours : ∀ z, csp.adjacent h z = true → z = parent ∨ z = child)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (child_adjacent : csp.adjacent h child = true) (child_later : earlier_in order h child = true)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (reduced : is_rule_two_selection csp originals order tuple h parent child selected) :
    is_selection_over csp originals order tuple
      (Function.update selected h fun b =>
        decide (∃ c : Fin (csp.domain_size child),
          csp.allowed h child b c = true ∧ selected child c = true)) := by
  obtain ⟨_, fixed, supported, joined⟩ := reduced
  have parent_ne : parent ≠ h := adjacent_ne csp parent h parent_adjacent
  have child_ne : child ≠ h := fun child_is_h => adjacent_ne csp h child child_adjacent child_is_h.symm
  constructor
  · intro x on_x a
    have x_ne : x ≠ h := by
      intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    rw [Function.update_of_ne x_ne]
    exact fixed x on_x a
  · intro x y adjacent_x_y x_earlier a a_selected
    by_cases x_is_h : x = h
    · subst x_is_h
      rcases two_neighbours y adjacent_x_y with y_is_parent | y_is_child
      · subst y_is_parent
        exact (not_earlier_both_ways order x y x_earlier parent_earlier).elim
      · subst y_is_child
        rw [Function.update_self] at a_selected
        obtain ⟨c, allowed_c, c_selected⟩ := of_decide_eq_true a_selected
        exact ⟨c, allowed_c, by rw [Function.update_of_ne child_ne]; exact c_selected⟩
    · rw [Function.update_of_ne x_is_h] at a_selected
      by_cases y_is_h : y = h
      · subst y_is_h
        have x_adjacent : csp.adjacent y x = true := by
          rw [csp.adjacent_symm]
          exact adjacent_x_y
        rcases two_neighbours x x_adjacent with x_is_parent | x_is_child
        · subst x_is_parent
          obtain ⟨c, ⟨b, allowed_b, allowed_c⟩, c_selected⟩ := joined a a_selected
          refine ⟨b, allowed_b, ?_⟩
          rw [Function.update_self]
          exact decide_eq_true ⟨c, allowed_c, c_selected⟩
        · subst x_is_child
          exact (not_earlier_both_ways order y x child_later x_earlier).elim
      · obtain ⟨b, allowed_b, b_selected⟩ :=
          supported x y x_is_h y_is_h adjacent_x_y x_earlier a a_selected
        exact ⟨b, allowed_b, by rw [Function.update_of_ne y_is_h]; exact b_selected⟩

open Classical in
theorem rule_two_minimal_support_count_le (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h parent child : Fin vertex_count)
    (h_hidden : originals h = false)
    (two_neighbours : ∀ z, csp.adjacent h z = true → z = parent ∨ z = child)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (child_adjacent : csp.adjacent h child = true) (child_later : earlier_in order h child = true) :
    Fintype.card {selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool //
        is_rule_two_selection csp originals order tuple h parent child selected} ≤
      models_over_tuple csp originals originals (minimal_support_encoding csp originals order)
        tuple := by
  classical
  rw [minimal_support_models_over_tuple_eq_selection_count]
  refine Fintype.card_le_of_surjective
    (fun selection => ⟨Function.update selection.val h fun _ => false,
      rule_two_forget_is_selection csp originals order tuple h parent child h_hidden
        parent_adjacent parent_earlier child_adjacent child_later selection.val
        selection.property⟩) ?_
  rintro ⟨reduced, reduced_property⟩
  refine ⟨⟨_, rule_two_lift_is_selection csp originals order tuple h parent child h_hidden
    two_neighbours parent_adjacent parent_earlier child_adjacent child_later reduced
    reduced_property⟩, ?_⟩
  apply Subtype.ext
  show Function.update (Function.update reduced h _) h (fun _ => false) = reduced
  rw [Function.update_idem]
  have at_h : reduced h = fun _ => false := funext reduced_property.1
  rw [← at_h, Function.update_eq_self]

end parsimony
