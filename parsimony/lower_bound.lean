import parsimony.minimal_support_counting

namespace parsimony

variable {vertex_count : ℕ}

inductive is_below (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (top : Fin vertex_count) : Fin vertex_count → Prop
  | child (y : Fin vertex_count) (adjacent_top_y : csp.adjacent top y = true)
      (top_earlier : earlier_in order top y = true) : is_below csp order top y
  | step (x y : Fin vertex_count) (below_x : is_below csp order top x)
      (adjacent_x_y : csp.adjacent x y = true) (x_earlier : earlier_in order x y = true) :
      is_below csp order top y

theorem is_below_position (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (top z : Fin vertex_count) (below : is_below csp order top z) :
    order.idxOf top < order.idxOf z := by
  induction below with
  | child y _ top_earlier => simpa [earlier_in] using top_earlier
  | step x y _ _ x_earlier top_before_x =>
    have x_before_y : order.idxOf x < order.idxOf y := by simpa [earlier_in] using x_earlier
    omega

theorem parent_of_below (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (top x y : Fin vertex_count)
    (below_y : is_below csp order top y) (adjacent_x_y : csp.adjacent x y = true)
    (x_earlier : earlier_in order x y = true) : x = top ∨ is_below csp order top x := by
  cases below_y with
  | child _ adjacent_top_y top_earlier =>
    left
    exact earlier_neighbour_unique csp order tree_order y x top adjacent_x_y x_earlier
      adjacent_top_y top_earlier
  | step z _ below_z adjacent_z_y z_earlier =>
    right
    have x_is_z := earlier_neighbour_unique csp order tree_order y x z adjacent_x_y x_earlier
      adjacent_z_y z_earlier
    rw [x_is_z]
    exact below_z

open Classical in
noncomputable def lower_bound_selection (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h : Fin vertex_count) (extension : assignment csp)
    (extra : Finset (Fin (csp.domain_size h))) :
    ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool :=
  Function.update
    (fun x a => if is_below csp order h x then decide (in_upward_set csp originals order tuple x a)
      else decide (a = extension x))
    h (fun a => decide (a = extension h ∨ a ∈ extra))

open Classical in
theorem lower_bound_selection_is_selection (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (h : Fin vertex_count) (h_hidden : originals h = false)
    (tuple : original_tuple csp originals) (extension : assignment csp)
    (extension_solution : is_solution csp extension)
    (extension_restricted : restrict_to_originals csp originals extension = tuple)
    (extra : Finset (Fin (csp.domain_size h)))
    (extra_inside : ∀ a ∈ extra, in_upward_set csp originals order tuple h a) :
    is_selection_over csp originals order tuple
      (lower_bound_selection csp originals order tuple h extension extra) := by
  have extension_upward : ∀ x, in_upward_set csp originals order tuple x (extension x) := by
    intro x
    have upward := extension_in_upward_set csp originals order tree_order extension
      extension_solution x
    rw [extension_restricted] at upward
    exact upward
  have value_off : ∀ x (x_ne : x ≠ h) (a : Fin (csp.domain_size x)),
      lower_bound_selection csp originals order tuple h extension extra x a =
        if is_below csp order h x then decide (in_upward_set csp originals order tuple x a)
        else decide (a = extension x) := by
    intro x x_ne a
    unfold lower_bound_selection
    rw [Function.update_of_ne x_ne]
  have value_at : ∀ a, lower_bound_selection csp originals order tuple h extension extra h a =
      decide (a = extension h ∨ a ∈ extra) := by
    intro a
    unfold lower_bound_selection
    rw [Function.update_self]
  have below_ne : ∀ z, is_below csp order h z → z ≠ h := by
    intro z below_z z_is_h
    have position := is_below_position csp order h z below_z
    rw [z_is_h] at position
    exact lt_irrefl _ position
  have selected_at_h_upward : ∀ a, lower_bound_selection csp originals order tuple h extension extra h a = true →
      in_upward_set csp originals order tuple h a := by
    intro a a_selected
    rw [value_at] at a_selected
    rcases (by simpa using a_selected : a = extension h ∨ a ∈ extra) with a_is | a_extra
    · rw [a_is]
      exact extension_upward h
    · exact extra_inside a a_extra
  constructor
  · intro x on_x a
    have x_ne : x ≠ h := by
      intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    have extension_x : extension x = tuple ⟨x, on_x⟩ := congrFun extension_restricted ⟨x, on_x⟩
    rw [value_off x x_ne a]
    split_ifs
    · have same : in_upward_set csp originals order tuple x a ↔ a = tuple ⟨x, on_x⟩ := by
        constructor
        · intro upward
          exact ((in_upward_set_iff csp originals order tuple x a).mp upward).1 on_x
        · intro a_is
          rw [a_is, ← extension_x]
          exact extension_upward x
      by_cases a_is : a = tuple ⟨x, on_x⟩
      · have upward : in_upward_set csp originals order tuple x a := same.mpr a_is
        rw [decide_eq_true upward, decide_eq_true a_is]
      · have not_upward : ¬ in_upward_set csp originals order tuple x a :=
          fun upward => a_is (same.mp upward)
        rw [decide_eq_false not_upward, decide_eq_false a_is]
    · rw [extension_x]
  · intro x y adjacent_x_y x_earlier a a_selected
    by_cases x_is_h : x = h
    · subst x
      have y_below : is_below csp order h y := is_below.child y adjacent_x_y x_earlier
      have y_ne := below_ne y y_below
      obtain ⟨_, witnesses⟩ := (in_upward_set_iff csp originals order tuple h a).mp
        (selected_at_h_upward a a_selected)
      obtain ⟨b, allowed_b, upward_b⟩ := witnesses y adjacent_x_y x_earlier
      refine ⟨b, allowed_b, ?_⟩
      rw [value_off y y_ne b]
      simpa [y_below] using upward_b
    · rw [value_off x x_is_h a] at a_selected
      by_cases x_below : is_below csp order h x
      · simp only [x_below, ↓reduceIte] at a_selected
        have upward_a : in_upward_set csp originals order tuple x a := by simpa using a_selected
        obtain ⟨_, witnesses⟩ := (in_upward_set_iff csp originals order tuple x a).mp upward_a
        obtain ⟨b, allowed_b, upward_b⟩ := witnesses y adjacent_x_y x_earlier
        have y_below : is_below csp order h y := is_below.step x y x_below adjacent_x_y x_earlier
        refine ⟨b, allowed_b, ?_⟩
        rw [value_off y (below_ne y y_below) b]
        simpa [y_below] using upward_b
      · simp only [x_below, ↓reduceIte] at a_selected
        have a_is : a = extension x := by simpa using a_selected
        by_cases y_is_h : y = h
        · subst y
          refine ⟨extension h, ?_, ?_⟩
          · rw [a_is]
            exact extension_solution x h adjacent_x_y
          · rw [value_at]
            simp
        · have y_not_below : ¬ is_below csp order h y := by
            intro y_below
            rcases parent_of_below csp order tree_order h x y y_below adjacent_x_y x_earlier with
              x_is | x_below'
            · exact x_is_h x_is
            · exact x_below x_below'
          refine ⟨extension y, ?_, ?_⟩
          · rw [a_is]
            exact extension_solution x y adjacent_x_y
          · rw [value_off y y_is_h]
            simp [y_not_below]

open Classical in
theorem minimal_support_lower_bound (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (h : Fin vertex_count) (h_hidden : originals h = false)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple) :
    2 ^ ((Finset.univ.filter fun a => in_upward_set csp originals order tuple h a).card - 1) ≤
      models_over_tuple csp originals originals (minimal_support_encoding csp originals order)
        tuple := by
  obtain ⟨extension, extension_solution, extension_restricted⟩ := in_rel
  let upward := Finset.univ.filter fun a => in_upward_set csp originals order tuple h a
  have extension_mem : extension h ∈ upward := by
    have upward_h := extension_in_upward_set csp originals order tree_order extension
      extension_solution h
    rw [extension_restricted] at upward_h
    simpa [upward] using upward_h
  rw [minimal_support_models_over_tuple_eq_selection_count]
  have subsets_count : Fintype.card {extra : Finset (Fin (csp.domain_size h)) //
      extra ⊆ upward.erase (extension h)} = 2 ^ (upward.card - 1) := by
    rw [Fintype.card_subtype]
    have filter_eq : (Finset.univ.filter fun extra : Finset (Fin (csp.domain_size h)) =>
        extra ⊆ upward.erase (extension h)) = (upward.erase (extension h)).powerset := by
      ext extra
      simp [Finset.mem_powerset]
    rw [filter_eq, Finset.card_powerset, Finset.card_erase_of_mem extension_mem]
  rw [← subsets_count]
  refine Fintype.card_le_of_injective (fun extra => ⟨lower_bound_selection csp originals order
    tuple h extension extra.val, lower_bound_selection_is_selection csp originals order tree_order
      h h_hidden tuple extension extension_solution extension_restricted extra.val
      (fun a a_extra => by
        have a_mem := Finset.mem_of_mem_erase (extra.property a_extra)
        simpa [upward] using a_mem)⟩) ?_
  intro first second same
  apply Subtype.ext
  ext a
  have at_h := congrFun (congrFun (congrArg Subtype.val same) h) a
  simp only [lower_bound_selection, Function.update_self] at at_h
  have first_ne : a ∈ first.val → a ≠ extension h := fun a_mem =>
    Finset.ne_of_mem_erase (first.property a_mem)
  have second_ne : a ∈ second.val → a ≠ extension h := fun a_mem =>
    Finset.ne_of_mem_erase (second.property a_mem)
  by_cases a_is : a = extension h
  · exact ⟨fun a_mem => absurd a_is (first_ne a_mem), fun a_mem => absurd a_is (second_ne a_mem)⟩
  · simpa [a_is] using at_h

end parsimony
