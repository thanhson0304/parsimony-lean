import parsimony.composition
import parsimony.minimal_support
import parsimony.partial_support

namespace parsimony

variable {vertex_count : ℕ}

theorem adjacent_ne (csp : binary_csp vertex_count) (x y : Fin vertex_count)
    (adjacent_x_y : csp.adjacent x y = true) : x ≠ y := by
  intro same
  subst same
  rw [csp.adjacent_irrefl] at adjacent_x_y
  exact absurd adjacent_x_y (by decide)

theorem earlier_or_later (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (x y : Fin vertex_count)
    (adjacent_x_y : csp.adjacent x y = true) :
    earlier_in order x y = true ∨ earlier_in order y x = true := by
  rcases Nat.lt_or_gt_of_ne (tree_order_positions_differ csp order tree_order x y
      (adjacent_ne csp x y adjacent_x_y)) with x_first | y_first
  · left
    simpa [earlier_in] using x_first
  · right
    simpa [earlier_in] using y_first

theorem earlier_neighbour_unique (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (y first second : Fin vertex_count)
    (first_adjacent : csp.adjacent first y = true) (first_earlier : earlier_in order first y = true)
    (second_adjacent : csp.adjacent second y = true)
    (second_earlier : earlier_in order second y = true) : first = second := by
  have first_lt : order.idxOf first < order.idxOf y := by simpa [earlier_in] using first_earlier
  have second_lt : order.idxOf second < order.idxOf y := by simpa [earlier_in] using second_earlier
  obtain ⟨parent, _, _, unique⟩ :=
    tree_order_unique_earlier_neighbour csp order tree_order y (by omega)
  rw [unique first first_adjacent first_lt, unique second second_adjacent second_lt]

def valuation_of_selection (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool) :
    boolean_variable csp originals → Bool
  | Sum.inl ⟨x, a⟩ => selected x a
  | Sum.inr ⟨⟨x, on_x⟩, i⟩ => decide (i.val < (tuple ⟨x, on_x⟩).val)

theorem valuation_of_selection_is_model (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (selection : is_selection_over csp originals order tuple selected) :
    is_model (valuation_of_selection csp originals tuple selected)
      (minimal_support_encoding csp originals order) := by
  rw [is_model_minimal_support_iff]
  exact ⟨fun x on_x => ⟨tuple ⟨x, on_x⟩, fun a => selection.1 x on_x a, fun _ => rfl⟩,
    fun x y adjacent_x_y x_earlier a a_selected =>
      selection.2 x y adjacent_x_y x_earlier a a_selected⟩

theorem valuation_of_selection_encodes (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (selection : is_selection_over csp originals order tuple selected) :
    encodes_tuple csp originals originals (valuation_of_selection csp originals tuple selected) tuple :=
  fun x a => selection.1 x.val x.property a

theorem minimal_support_models_over_tuple_eq_selection_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) :
    models_over_tuple csp originals originals (minimal_support_encoding csp originals order) tuple =
      Fintype.card {selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool //
        is_selection_over csp originals order tuple selected} := by
  unfold models_over_tuple
  symm
  refine Fintype.card_of_bijective
    (f := fun selection => ⟨valuation_of_selection csp originals tuple selection.val,
      valuation_of_selection_is_model csp originals order tuple selection.val selection.property,
      valuation_of_selection_encodes csp originals order tuple selection.val
        selection.property⟩) ⟨?_, ?_⟩
  · intro first second same
    apply Subtype.ext
    funext x a
    exact congrFun (congrArg Subtype.val same) (Sum.inl ⟨x, a⟩)
  · rintro ⟨valuation, model, encodes⟩
    obtain ⟨blocks, edges⟩ := (is_model_minimal_support_iff csp originals order valuation).mp model
    have selection : is_selection_over csp originals order tuple
        (fun x a => valuation (Sum.inl ⟨x, a⟩)) :=
      ⟨fun x on_x a => encodes ⟨x, on_x⟩ a,
        fun x y adjacent_x_y x_earlier a a_selected => edges x y adjacent_x_y x_earlier a a_selected⟩
    refine ⟨⟨_, selection⟩, Subtype.ext ?_⟩
    funext variable_name
    rcases variable_name with ⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩
    · rfl
    · obtain ⟨chosen, values_fixed, ladder_fixed⟩ := blocks x on_x
      have chosen_true : decide (chosen = tuple ⟨x, on_x⟩) = decide (chosen = chosen) :=
        (encodes ⟨x, on_x⟩ chosen).symm.trans (values_fixed chosen)
      have chosen_is_tuple : chosen = tuple ⟨x, on_x⟩ := by simpa using chosen_true
      show decide (i.val < (tuple ⟨x, on_x⟩).val) = valuation (Sum.inr ⟨⟨x, on_x⟩, i⟩)
      rw [ladder_fixed i, chosen_is_tuple]

theorem partial_support_model_is_minimal_support_model (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (partial_support_encoding csp originals)) :
    is_model valuation (minimal_support_encoding csp originals order) := by
  rw [is_model_partial_support_iff] at model
  rw [is_model_minimal_support_iff]
  exact ⟨model.1, fun x y adjacent_x_y _ => model.2 x y adjacent_x_y⟩

theorem partial_support_models_le_minimal_support (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) :
    models_over_tuple csp originals originals (partial_support_encoding csp originals) tuple ≤
      models_over_tuple csp originals originals (minimal_support_encoding csp originals order)
        tuple := by
  unfold models_over_tuple
  exact Fintype.card_le_of_injective
    (fun valuation => ⟨valuation.val, partial_support_model_is_minimal_support_model csp originals
      order _ valuation.property.1, valuation.property.2⟩)
    (fun first second same => Subtype.ext (by
      have same_values := congrArg Subtype.val same
      exact same_values))

theorem hidden_leaf_upward_set_is_domain (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tuple : original_tuple csp originals) (h : Fin vertex_count) (h_hidden : originals h = false)
    (no_child : ∀ y, csp.adjacent h y = true → earlier_in order h y = false)
    (a : Fin (csp.domain_size h)) : in_upward_set csp originals order tuple h a := by
  rw [in_upward_set_iff]
  refine ⟨fun on_h => absurd on_h (by simp [h_hidden]), fun y adjacent_h_y h_earlier => ?_⟩
  rw [no_child y adjacent_h_y] at h_earlier
  exact absurd h_earlier (by decide)

theorem minimal_support_not_parsimonious_of_hidden_leaf (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (h : Fin vertex_count) (h_hidden : originals h = false)
    (no_child : ∀ y, csp.adjacent h y = true → earlier_in order h y = false)
    (two_values : 2 ≤ csp.domain_size h)
    (nonempty_relation : ∃ tuple, in_relation csp originals tuple) :
    ¬ is_parsimonious csp originals (minimal_support_encoding csp originals order) := by
  rw [minimal_support_parsimonious_iff csp originals order tree_order root_original]
  intro all_unique
  obtain ⟨tuple, in_rel⟩ := nonempty_relation
  obtain ⟨value, _, unique⟩ := all_unique tuple in_rel h h_hidden
  have zero_is := unique ⟨0, by omega⟩
    (hidden_leaf_upward_set_is_domain csp originals order tuple h h_hidden no_child _)
  have one_is := unique ⟨1, by omega⟩
    (hidden_leaf_upward_set_is_domain csp originals order tuple h h_hidden no_child _)
  have zero_is_one := zero_is.trans one_is.symm
  simp [Fin.ext_iff] at zero_is_one

theorem minimal_support_model_contains_unique_extension (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (minimal_support_encoding csp originals order))
    (tuple : original_tuple csp originals)
    (encodes : encodes_tuple csp originals originals valuation tuple)
    (candidate : assignment csp) (solution : is_solution csp candidate)
    (restricted : restrict_to_originals csp originals candidate = tuple)
    (unique : extension_count csp originals tuple = 1) :
    ∀ x, valuation (Sum.inl ⟨x, candidate x⟩) = true := by
  obtain ⟨other, other_solution, other_selected⟩ :=
    minimal_support_model_has_supported_solution csp originals order tree_order root_original
      valuation model
  have other_restricted : restrict_to_originals csp originals other = tuple := by
    funext x
    have selected := other_selected x.val
    have fixed := encodes x (other x.val)
    rw [selected] at fixed
    show other x.val = tuple x
    simpa using fixed.symm
  obtain ⟨only, _, only_unique⟩ := (extension_count_eq_one_iff csp originals tuple).mp unique
  have other_is := only_unique other ⟨other_solution, other_restricted⟩
  have candidate_is := only_unique candidate ⟨solution, restricted⟩
  have same : candidate = other := candidate_is.trans other_is.symm
  rw [same]
  exact other_selected

section one_hidden

variable (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
  (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
  (h parent : Fin vertex_count) (h_hidden : originals h = false)
  (only_hidden : ∀ x, originals x = false → x = h)
  (parent_adjacent : csp.adjacent parent h = true)
  (parent_earlier : earlier_in order parent h = true)
  (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple)

include only_hidden in
theorem original_of_ne_hidden (x : Fin vertex_count) (x_ne : x ≠ h) : originals x = true := by
  by_contra not_on
  exact x_ne (only_hidden x (by simpa using not_on))

include in_rel in
theorem original_edges_allowed (x y : Fin vertex_count) (on_x : originals x = true)
    (on_y : originals y = true) (adjacent_x_y : csp.adjacent x y = true) :
    csp.allowed x y (tuple ⟨x, on_x⟩) (tuple ⟨y, on_y⟩) = true := by
  obtain ⟨candidate, solution, restricted⟩ := in_rel
  have x_value : candidate x = tuple ⟨x, on_x⟩ := congrFun restricted ⟨x, on_x⟩
  have y_value : candidate y = tuple ⟨y, on_y⟩ := congrFun restricted ⟨y, on_y⟩
  rw [← x_value, ← y_value]
  exact solution x y adjacent_x_y

include only_hidden parent_adjacent parent_earlier in
theorem selection_at_only_hidden
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool)
    (selection : is_selection_over csp originals order tuple selected) :
    (∀ b, selected h b = true → b ∈ children_compatible_values csp originals order tuple h) ∧
      ∃ b, selected h b = true ∧ b ∈ parent_compatible_values csp originals order tuple h parent := by
  have children_part : ∀ b, selected h b = true →
      b ∈ children_compatible_values csp originals order tuple h := by
    intro b b_selected
    simp only [children_compatible_values, Finset.mem_filter, Finset.mem_univ, true_and]
    intro c adjacent_h_c h_earlier on_c
    obtain ⟨other, allowed_other, selected_other⟩ :=
      selection.2 h c adjacent_h_c h_earlier b b_selected
    have fixed := selection.1 c on_c other
    rw [selected_other] at fixed
    have other_is_tuple : other = tuple ⟨c, on_c⟩ := by simpa using fixed.symm
    rw [← other_is_tuple]
    exact allowed_other
  refine ⟨children_part, ?_⟩
  have parent_original : originals parent = true :=
    original_of_ne_hidden originals h only_hidden parent
      (adjacent_ne csp parent h parent_adjacent)
  have parent_selected : selected parent (tuple ⟨parent, parent_original⟩) = true := by
    rw [selection.1 parent parent_original]
    simp
  obtain ⟨b, allowed_b, selected_b⟩ :=
    selection.2 parent h parent_adjacent parent_earlier _ parent_selected
  refine ⟨b, selected_b, ?_⟩
  simp only [parent_compatible_values, Finset.mem_filter]
  exact ⟨children_part b selected_b, fun _ => allowed_b⟩

def selection_with_hidden_values
    (chosen : Fin (csp.domain_size h) → Bool) : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool :=
  Function.update (fun x a => if on_x : originals x = true then decide (a = tuple ⟨x, on_x⟩) else false)
    h chosen

include tree_order only_hidden h_hidden parent_adjacent parent_earlier in_rel in
theorem selection_with_hidden_values_is_selection (chosen : Fin (csp.domain_size h) → Bool)
    (inside : ∀ b, chosen b = true → b ∈ children_compatible_values csp originals order tuple h)
    (meets : ∃ b, chosen b = true ∧ b ∈ parent_compatible_values csp originals order tuple h parent) :
    is_selection_over csp originals order tuple
      (selection_with_hidden_values csp originals h tuple chosen) := by
  have value_off_hidden : ∀ x (x_ne : x ≠ h) (a : Fin (csp.domain_size x)),
      selection_with_hidden_values csp originals h tuple chosen x a =
        decide (a = tuple ⟨x, original_of_ne_hidden originals h only_hidden x x_ne⟩) := by
    intro x x_ne a
    unfold selection_with_hidden_values
    rw [Function.update_of_ne x_ne]
    simp [original_of_ne_hidden originals h only_hidden x x_ne]
  have value_at_hidden : ∀ a, selection_with_hidden_values csp originals h tuple chosen h a =
      chosen a := by
    intro a
    unfold selection_with_hidden_values
    rw [Function.update_self]
  constructor
  · intro x on_x a
    have x_ne : x ≠ h := by
      intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    rw [value_off_hidden x x_ne a]
  · intro x y adjacent_x_y x_earlier a a_selected
    by_cases x_is_h : x = h
    · subst x
      rw [value_at_hidden] at a_selected
      have y_ne : y ≠ h := (adjacent_ne csp h y adjacent_x_y).symm
      have on_y := original_of_ne_hidden originals h only_hidden y y_ne
      refine ⟨tuple ⟨y, on_y⟩, ?_, ?_⟩
      · have a_inside := inside a a_selected
        simp only [children_compatible_values, Finset.mem_filter, Finset.mem_univ, true_and] at a_inside
        exact a_inside y adjacent_x_y x_earlier on_y
      · rw [value_off_hidden y y_ne]
        simp
    · have on_x := original_of_ne_hidden originals h only_hidden x x_is_h
      rw [value_off_hidden x x_is_h a] at a_selected
      have a_is_tuple : a = tuple ⟨x, on_x⟩ := by simpa using a_selected
      by_cases y_is_h : y = h
      · subst y
        have x_is_parent : x = parent :=
          earlier_neighbour_unique csp order tree_order h x parent adjacent_x_y x_earlier
            parent_adjacent parent_earlier
        subst x
        obtain ⟨b, b_chosen, b_meets⟩ := meets
        refine ⟨b, ?_, by rw [value_at_hidden]; exact b_chosen⟩
        simp only [parent_compatible_values, Finset.mem_filter] at b_meets
        rw [a_is_tuple]
        exact b_meets.2 on_x
      · have on_y := original_of_ne_hidden originals h only_hidden y y_is_h
        refine ⟨tuple ⟨y, on_y⟩, ?_, ?_⟩
        · rw [a_is_tuple]
          exact original_edges_allowed csp originals tuple in_rel x y on_x on_y adjacent_x_y
        · rw [value_off_hidden y y_is_h]
          simp

include tree_order only_hidden h_hidden parent_adjacent parent_earlier in_rel in
theorem one_hidden_selection_count :
    Fintype.card {selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool //
        is_selection_over csp originals order tuple selected} =
      Fintype.card {chosen : Fin (csp.domain_size h) → Bool //
        (∀ b, chosen b = true → b ∈ children_compatible_values csp originals order tuple h) ∧
          ∃ b, chosen b = true ∧
            b ∈ parent_compatible_values csp originals order tuple h parent} := by
  refine Fintype.card_of_bijective
    (f := fun selection => ⟨selection.val h,
      selection_at_only_hidden csp originals order h parent only_hidden parent_adjacent
        parent_earlier tuple selection.val selection.property⟩) ⟨?_, ?_⟩
  · intro first second same
    apply Subtype.ext
    funext x a
    by_cases x_is_h : x = h
    · subst x
      exact congrFun (congrArg Subtype.val same) a
    · have on_x := original_of_ne_hidden originals h only_hidden x x_is_h
      rw [first.property.1 x on_x a, second.property.1 x on_x a]
  · rintro ⟨chosen, inside, meets⟩
    refine ⟨⟨selection_with_hidden_values csp originals h tuple chosen,
      selection_with_hidden_values_is_selection csp originals order tree_order h parent h_hidden
        only_hidden parent_adjacent parent_earlier tuple in_rel chosen inside meets⟩, ?_⟩
    apply Subtype.ext
    funext a
    show selection_with_hidden_values csp originals h tuple chosen h a = chosen a
    unfold selection_with_hidden_values
    rw [Function.update_self]

end one_hidden

theorem subsets_meeting_count {size : ℕ} (upper lower : Finset (Fin size))
    (lower_subset : lower ⊆ upper) :
    Fintype.card {chosen : Fin size → Bool //
        (∀ b, chosen b = true → b ∈ upper) ∧ ∃ b, chosen b = true ∧ b ∈ lower} =
      2 ^ upper.card - 2 ^ (upper.card - lower.card) := by
  have as_finsets : Fintype.card {chosen : Fin size → Bool //
        (∀ b, chosen b = true → b ∈ upper) ∧ ∃ b, chosen b = true ∧ b ∈ lower} =
      Fintype.card {subset : Finset (Fin size) // subset ⊆ upper ∧ (subset ∩ lower).Nonempty} := by
    symm
    refine Fintype.card_of_bijective
      (f := fun subset => ⟨fun b => decide (b ∈ subset.val),
        fun b b_chosen => subset.property.1 (by simpa using b_chosen), by
          obtain ⟨b, b_mem⟩ := subset.property.2
          rw [Finset.mem_inter] at b_mem
          exact ⟨b, by simpa using b_mem.1, b_mem.2⟩⟩) ⟨?_, ?_⟩
    · intro first second same
      apply Subtype.ext
      ext b
      have := congrFun (congrArg Subtype.val same) b
      simpa using this
    · rintro ⟨chosen, inside, meets⟩
      refine ⟨⟨Finset.univ.filter fun b => chosen b = true, ?_, ?_⟩, ?_⟩
      · intro b b_mem
        exact inside b (by simpa using b_mem)
      · obtain ⟨b, b_chosen, b_lower⟩ := meets
        exact ⟨b, Finset.mem_inter.mpr ⟨by simpa using b_chosen, b_lower⟩⟩
      · apply Subtype.ext
        funext b
        cases chosen_b : chosen b <;> simp [chosen_b]
  rw [as_finsets, Fintype.card_subtype]
  have filter_eq : (Finset.univ.filter fun subset : Finset (Fin size) =>
        subset ⊆ upper ∧ (subset ∩ lower).Nonempty) =
      upper.powerset.filter fun subset => (subset ∩ lower).Nonempty := by
    ext subset
    simp [Finset.mem_powerset]
  have missing_eq : (upper.powerset.filter fun subset : Finset (Fin size) =>
        ¬ (subset ∩ lower).Nonempty) = (upper \ lower).powerset := by
    ext subset
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.subset_sdiff, Finset.disjoint_iff_inter_eq_empty]
  have split := Finset.card_filter_add_card_filter_not
    (s := upper.powerset) (fun subset : Finset (Fin size) => (subset ∩ lower).Nonempty)
  rw [missing_eq, Finset.card_powerset, Finset.card_powerset,
    Finset.card_sdiff_of_subset lower_subset] at split
  rw [filter_eq]
  omega

theorem one_hidden_model_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (h parent : Fin vertex_count)
    (h_hidden : originals h = false) (only_hidden : ∀ x, originals x = false → x = h)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple) :
    models_over_tuple csp originals originals (minimal_support_encoding csp originals order) tuple =
      2 ^ (children_compatible_values csp originals order tuple h).card -
        2 ^ ((children_compatible_values csp originals order tuple h).card -
          (parent_compatible_values csp originals order tuple h parent).card) := by
  rw [minimal_support_models_over_tuple_eq_selection_count,
    one_hidden_selection_count csp originals order tree_order h parent h_hidden only_hidden
      parent_adjacent parent_earlier tuple in_rel]
  exact subsets_meeting_count _ _ (Finset.filter_subset _ _)

theorem parent_compatible_count_eq_extension_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (h parent : Fin vertex_count)
    (h_hidden : originals h = false) (only_hidden : ∀ x, originals x = false → x = h)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple) :
    (parent_compatible_values csp originals order tuple h parent).card =
      extension_count csp originals tuple := by
  obtain ⟨extension, extension_solution, extension_restricted⟩ := in_rel
  have extension_value : ∀ x (on_x : originals x = true), extension x = tuple ⟨x, on_x⟩ :=
    fun x on_x => congrFun extension_restricted ⟨x, on_x⟩
  unfold extension_count
  rw [← Fintype.card_coe]
  symm
  refine Fintype.card_of_bijective
    (f := fun candidate => ⟨candidate.val h, by
      obtain ⟨candidate_solution, candidate_restricted⟩ := candidate.property
      have candidate_value : ∀ x (on_x : originals x = true), candidate.val x = tuple ⟨x, on_x⟩ :=
        fun x on_x => congrFun candidate_restricted ⟨x, on_x⟩
      simp only [parent_compatible_values, children_compatible_values, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨fun c adjacent_h_c _ on_c => ?_, fun on_parent => ?_⟩
      · rw [← candidate_value c on_c]
        exact candidate_solution h c adjacent_h_c
      · rw [← candidate_value parent on_parent]
        exact candidate_solution parent h parent_adjacent⟩) ⟨?_, ?_⟩
  · intro first second same
    apply Subtype.ext
    funext x
    by_cases x_is_h : x = h
    · subst x
      exact congrArg Subtype.val same
    · have on_x := original_of_ne_hidden originals h only_hidden x x_is_h
      exact (congrFun first.property.2 ⟨x, on_x⟩).trans (congrFun second.property.2 ⟨x, on_x⟩).symm
  · rintro ⟨value, value_mem⟩
    simp only [parent_compatible_values, children_compatible_values, Finset.mem_filter,
      Finset.mem_univ, true_and] at value_mem
    obtain ⟨value_children, value_parent⟩ := value_mem
    have updated_off : ∀ x, x ≠ h → Function.update extension h value x = extension x :=
      fun x x_ne => Function.update_of_ne x_ne _ _
    have updated_at : Function.update extension h value h = value := Function.update_self _ _ _
    refine ⟨⟨Function.update extension h value, ?_, ?_⟩, ?_⟩
    · intro x y adjacent_x_y
      by_cases x_is_h : x = h
      · subst x
        have y_ne : y ≠ h := (adjacent_ne csp h y adjacent_x_y).symm
        have on_y := original_of_ne_hidden originals h only_hidden y y_ne
        rw [updated_at, updated_off y y_ne, extension_value y on_y]
        rcases earlier_or_later csp order tree_order h y adjacent_x_y with h_first | y_first
        · exact value_children y adjacent_x_y h_first on_y
        · have y_is_parent : y = parent :=
            earlier_neighbour_unique csp order tree_order h y parent
              (by rw [csp.adjacent_symm]; exact adjacent_x_y) y_first parent_adjacent parent_earlier
          subst y
          rw [csp.allowed_symm h parent]
          exact value_parent on_y
      · by_cases y_is_h : y = h
        · subst y
          have on_x := original_of_ne_hidden originals h only_hidden x x_is_h
          rw [updated_at, updated_off x x_is_h, extension_value x on_x]
          rcases earlier_or_later csp order tree_order x h adjacent_x_y with x_first | h_first
          · have x_is_parent : x = parent :=
              earlier_neighbour_unique csp order tree_order h x parent adjacent_x_y x_first
                parent_adjacent parent_earlier
            subst x
            exact value_parent on_x
          · rw [csp.allowed_symm x h]
            exact value_children x (by rw [csp.adjacent_symm]; exact adjacent_x_y) h_first on_x
        · rw [updated_off x x_is_h, updated_off y y_is_h]
          exact extension_solution x y adjacent_x_y
    · funext x
      have x_ne : x.val ≠ h := by
        intro x_is_h
        have on_x := x.property
        rw [x_is_h, h_hidden] at on_x
        exact absurd on_x (by decide)
      show Function.update extension h value x.val = tuple x
      rw [updated_off x.val x_ne]
      exact extension_value x.val x.property
    · apply Subtype.ext
      exact updated_at

theorem one_hidden_model_count_of_unique_extension (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (h parent : Fin vertex_count)
    (h_hidden : originals h = false) (only_hidden : ∀ x, originals x = false → x = h)
    (parent_adjacent : csp.adjacent parent h = true)
    (parent_earlier : earlier_in order parent h = true)
    (unique : has_unique_extension csp originals)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple) :
    models_over_tuple csp originals originals (minimal_support_encoding csp originals order) tuple =
      2 ^ ((children_compatible_values csp originals order tuple h).card - 1) := by
  have parent_one : (parent_compatible_values csp originals order tuple h parent).card = 1 := by
    rw [parent_compatible_count_eq_extension_count csp originals order tree_order h parent
      h_hidden only_hidden parent_adjacent parent_earlier tuple in_rel]
    exact unique tuple in_rel
  have children_positive : 1 ≤ (children_compatible_values csp originals order tuple h).card := by
    have parent_le := Finset.card_le_card
      (show parent_compatible_values csp originals order tuple h parent ⊆
        children_compatible_values csp originals order tuple h from Finset.filter_subset _ _)
    omega
  rw [one_hidden_model_count csp originals order tree_order h parent h_hidden only_hidden
    parent_adjacent parent_earlier tuple in_rel, parent_one]
  obtain ⟨smaller, smaller_eq⟩ : ∃ smaller,
      (children_compatible_values csp originals order tuple h).card = smaller + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos children_positive).symm⟩
  rw [smaller_eq, Nat.add_sub_cancel, pow_succ]
  omega

end parsimony
