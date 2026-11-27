import parsimony.minimal_support_counting

namespace parsimony

variable {vertex_count : ℕ}

section decomposition

variable (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
  (h : Fin vertex_count)

def rest_of_assignment (candidate : assignment csp) : rest_assignment csp h :=
  fun x => candidate x.val

def assemble (rest : rest_assignment csp h) (value : Fin (csp.domain_size h)) : assignment csp :=
  Function.update (fun x => if x_is_h : x = h then ⟨0, csp.domain_nonempty x⟩ else rest ⟨x, x_is_h⟩)
    h value

theorem assemble_at (rest : rest_assignment csp h) (value : Fin (csp.domain_size h)) :
    assemble csp h rest value h = value := by
  unfold assemble
  rw [Function.update_self]

theorem assemble_off (rest : rest_assignment csp h) (value : Fin (csp.domain_size h))
    (x : Fin vertex_count) (x_ne : x ≠ h) : assemble csp h rest value x = rest ⟨x, x_ne⟩ := by
  unfold assemble
  rw [Function.update_of_ne x_ne]
  simp [x_ne]

theorem assemble_is_solution (rest : rest_assignment csp h) (value : Fin (csp.domain_size h))
    (consistent : rest_is_consistent csp h rest)
    (fits : value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest)) :
    is_solution csp (assemble csp h rest value) := by
  intro x y adjacent_x_y
  by_cases x_is_h : x = h
  · subst x
    have y_ne : y ≠ h := (adjacent_ne csp h y adjacent_x_y).symm
    rw [assemble_at, assemble_off csp h rest value y y_ne]
    exact fits ⟨y, adjacent_x_y⟩
  · by_cases y_is_h : y = h
    · subst y
      rw [assemble_at, assemble_off csp h rest value x x_is_h, csp.allowed_symm x h]
      exact fits ⟨x, by rw [csp.adjacent_symm]; exact adjacent_x_y⟩
    · rw [assemble_off csp h rest value x x_is_h, assemble_off csp h rest value y y_is_h]
      exact consistent ⟨x, x_is_h⟩ ⟨y, y_is_h⟩ adjacent_x_y

theorem assemble_restricts (h_hidden : originals h = false) (rest : rest_assignment csp h)
    (value : Fin (csp.domain_size h)) (tuple : original_tuple csp originals)
    (encodes : rest_encodes_tuple csp originals h rest tuple) :
    restrict_to_originals csp originals (assemble csp h rest value) = tuple := by
  funext x
  have x_ne : x.val ≠ h := by
    intro x_is_h
    have on_x := x.property
    rw [x_is_h, h_hidden] at on_x
    exact absurd on_x (by decide)
  show assemble csp h rest value x.val = tuple x
  rw [assemble_off csp h rest value x.val x_ne]
  exact encodes ⟨x.val, x_ne⟩ x.property

theorem rest_of_assemble (rest : rest_assignment csp h) (value : Fin (csp.domain_size h)) :
    rest_of_assignment csp h (assemble csp h rest value) = rest := by
  funext x
  exact assemble_off csp h rest value x.val x.property

theorem assemble_of_rest (candidate : assignment csp) :
    assemble csp h (rest_of_assignment csp h candidate) (candidate h) = candidate := by
  funext x
  by_cases x_is_h : x = h
  · subst x
    exact assemble_at csp h _ _
  · rw [assemble_off csp h _ _ x x_is_h]
    rfl

theorem rest_of_solution_consistent (candidate : assignment csp)
    (solution : is_solution csp candidate) :
    rest_is_consistent csp h (rest_of_assignment csp h candidate) :=
  fun x y adjacent_x_y => solution x.val y.val adjacent_x_y

theorem value_of_solution_fits (candidate : assignment csp) (solution : is_solution csp candidate) :
    value_fits_neighbours csp h (candidate h)
      (neighbour_tuple_of_rest csp h (rest_of_assignment csp h candidate)) :=
  fun y => solution h y.val y.property

theorem rest_of_extension_encodes (candidate : assignment csp) (tuple : original_tuple csp originals)
    (restricted : restrict_to_originals csp originals candidate = tuple) :
    rest_encodes_tuple csp originals h (rest_of_assignment csp h candidate) tuple :=
  fun x on_x => congrFun restricted ⟨x.val, on_x⟩

theorem extension_count_eq_sum (h_hidden : originals h = false)
    (tuple : original_tuple csp originals) :
    extension_count csp originals tuple =
      ∑ rest : {rest : rest_assignment csp h //
          rest_is_consistent csp h rest ∧ rest_encodes_tuple csp originals h rest tuple},
        old_value_count csp h (neighbour_tuple_of_rest csp h rest.val) := by
  unfold extension_count old_value_count
  rw [← Fintype.card_sigma]
  symm
  refine Fintype.card_of_bijective
    (f := fun pair => ⟨assemble csp h pair.1.val pair.2.val,
      assemble_is_solution csp h pair.1.val pair.2.val pair.1.property.1 pair.2.property,
      assemble_restricts csp originals h h_hidden pair.1.val pair.2.val tuple
        pair.1.property.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨first_rest, first_ok⟩, ⟨first_value, first_fits⟩⟩
      ⟨⟨second_rest, second_ok⟩, ⟨second_value, second_fits⟩⟩ same
    have same_assignment : assemble csp h first_rest first_value =
        assemble csp h second_rest second_value := congrArg Subtype.val same
    have rests_equal : first_rest = second_rest := by
      rw [← rest_of_assemble csp h first_rest first_value,
        ← rest_of_assemble csp h second_rest second_value, same_assignment]
    have values_equal : first_value = second_value := by
      rw [← assemble_at csp h first_rest first_value, ← assemble_at csp h second_rest second_value,
        same_assignment]
    subst rests_equal
    subst values_equal
    rfl
  · rintro ⟨candidate, solution, restricted⟩
    refine ⟨⟨⟨rest_of_assignment csp h candidate,
      rest_of_solution_consistent csp h candidate solution,
      rest_of_extension_encodes csp originals h candidate tuple restricted⟩,
      ⟨candidate h, value_of_solution_fits csp h candidate solution⟩⟩, ?_⟩
    exact Subtype.ext (assemble_of_rest csp h candidate)

theorem eliminated_count_le (h_hidden : originals h = false)
    (tuple : original_tuple csp originals) :
    eliminated_extension_count csp originals h tuple ≤ extension_count csp originals tuple := by
  unfold eliminated_extension_count extension_count
  refine Fintype.card_le_of_injective
    (fun rest => ⟨assemble csp h rest.val (Classical.choose rest.property.2.1),
      assemble_is_solution csp h rest.val _ rest.property.1
        (Classical.choose_spec rest.property.2.1),
      assemble_restricts csp originals h h_hidden rest.val _ tuple rest.property.2.2⟩) ?_
  intro first second same
  apply Subtype.ext
  have same_assignment := congrArg Subtype.val same
  simp only at same_assignment
  rw [← rest_of_assemble csp h first.val (Classical.choose first.property.2.1),
    ← rest_of_assemble csp h second.val (Classical.choose second.property.2.1), same_assignment]

theorem eliminated_count_pos_iff (h_hidden : originals h = false)
    (tuple : original_tuple csp originals) :
    0 < eliminated_extension_count csp originals h tuple ↔
      0 < extension_count csp originals tuple := by
  constructor
  · intro positive
    exact lt_of_lt_of_le positive (eliminated_count_le csp originals h h_hidden tuple)
  · intro positive
    unfold extension_count at positive
    obtain ⟨⟨candidate, solution, restricted⟩⟩ := Fintype.card_pos_iff.mp positive
    unfold eliminated_extension_count
    exact Fintype.card_pos_iff.mpr ⟨⟨rest_of_assignment csp h candidate,
      rest_of_solution_consistent csp h candidate solution,
      ⟨candidate h, value_of_solution_fits csp h candidate solution⟩,
      rest_of_extension_encodes csp originals h candidate tuple restricted⟩⟩

theorem eliminated_count_eq_sum (tuple : original_tuple csp originals) :
    eliminated_extension_count csp originals h tuple =
      ∑ rest : {rest : rest_assignment csp h //
          rest_is_consistent csp h rest ∧ rest_encodes_tuple csp originals h rest tuple},
        if ∃ value, value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest.val)
        then 1 else 0 := by
  unfold eliminated_extension_count
  have regroup : {rest : rest_assignment csp h // rest_is_consistent csp h rest ∧
      (∃ value, value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest)) ∧
      rest_encodes_tuple csp originals h rest tuple} ≃
      {rest : {rest : rest_assignment csp h //
          rest_is_consistent csp h rest ∧ rest_encodes_tuple csp originals h rest tuple} //
        ∃ value, value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest.val)} :=
    { toFun := fun rest => ⟨⟨rest.val, rest.property.1, rest.property.2.2⟩, rest.property.2.1⟩
      invFun := fun rest => ⟨rest.val.val, rest.val.property.1, rest.property, rest.val.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr regroup, Fintype.card_subtype, Finset.card_filter]

theorem eliminated_count_eq_iff (h_hidden : originals h = false)
    (tuple : original_tuple csp originals) :
    eliminated_extension_count csp originals h tuple = extension_count csp originals tuple ↔
      ∀ rest : rest_assignment csp h, rest_is_consistent csp h rest →
        rest_encodes_tuple csp originals h rest tuple →
          (∃ value, value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest)) →
            old_value_count csp h (neighbour_tuple_of_rest csp h rest) = 1 := by
  rw [eliminated_count_eq_sum, extension_count_eq_sum csp originals h h_hidden]
  have termwise : ∀ rest : {rest : rest_assignment csp h //
      rest_is_consistent csp h rest ∧ rest_encodes_tuple csp originals h rest tuple},
      (if ∃ value, value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest.val)
        then 1 else 0) ≤ old_value_count csp h (neighbour_tuple_of_rest csp h rest.val) := by
    intro rest
    split_ifs with fits_exists
    · obtain ⟨value, fits⟩ := fits_exists
      exact Fintype.card_pos_iff.mpr ⟨⟨value, fits⟩⟩
    · exact Nat.zero_le _
  rw [Finset.sum_eq_sum_iff_of_le fun rest _ => termwise rest]
  constructor
  · intro all_equal rest consistent encodes fits_exists
    have equal := all_equal ⟨rest, consistent, encodes⟩ (Finset.mem_univ _)
    rw [ite_eq_left fits_exists] at equal
    exact equal.symm
  · intro all_one rest _
    split_ifs with fits_exists
    · exact (all_one rest.val rest.property.1 rest.property.2 fits_exists).symm
    · symm
      unfold old_value_count
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun value => fits_exists ⟨value.val, value.property⟩⟩

theorem reconstructed_count_eq_sum (table : Finset (neighbour_box csp h))
    (tuple : original_tuple csp originals) :
    reconstructed_extension_count csp originals h table tuple =
      ∑ rest : {rest : rest_assignment csp h //
          rest_is_consistent csp h rest ∧ rest_encodes_tuple csp originals h rest tuple},
        box_count csp h table (neighbour_tuple_of_rest csp h rest.val) := by
  unfold reconstructed_extension_count
  have regroup : {pair : rest_assignment csp h × neighbour_box csp h //
      rest_is_consistent csp h pair.1 ∧ pair.2 ∈ table ∧
      box_represents csp h pair.2 (neighbour_tuple_of_rest csp h pair.1) ∧
      rest_encodes_tuple csp originals h pair.1 tuple} ≃
      Σ rest : {rest : rest_assignment csp h //
          rest_is_consistent csp h rest ∧ rest_encodes_tuple csp originals h rest tuple},
        {box : neighbour_box csp h //
          box ∈ table ∧ box_represents csp h box (neighbour_tuple_of_rest csp h rest.val)} :=
    { toFun := fun pair => ⟨⟨pair.val.1, pair.property.1, pair.property.2.2.2⟩,
        ⟨pair.val.2, pair.property.2.1, pair.property.2.2.1⟩⟩
      invFun := fun pair => ⟨(pair.1.val, pair.2.val), pair.1.property.1, pair.2.property.1,
        pair.2.property.2, pair.1.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr regroup, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun rest _ => ?_
  unfold box_count
  rw [Fintype.card_subtype]
  congr 1
  ext box
  simp

theorem eq_zero_iff_of_pos_iff {first second : ℕ} (same : 0 < first ↔ 0 < second) :
    first = 0 ↔ second = 0 := by
  constructor
  · intro first_zero
    by_contra second_ne
    have := same.mpr (Nat.pos_of_ne_zero second_ne)
    omega
  · intro second_zero
    by_contra first_ne
    have := same.mp (Nat.pos_of_ne_zero first_ne)
    omega

theorem box_count_pos_iff (table : Finset (neighbour_box csp h))
    (valid : is_valid_cc_table csp h table) (neighbours : neighbour_tuple csp h) :
    0 < box_count csp h table neighbours ↔ 0 < old_value_count csp h neighbours := by
  unfold box_count old_value_count
  rw [Finset.card_pos, Fintype.card_pos_iff]
  constructor
  · rintro ⟨box, box_mem⟩
    rw [Finset.mem_filter] at box_mem
    obtain ⟨value, fits⟩ := (valid neighbours).mpr ⟨box, box_mem.1, box_mem.2⟩
    exact ⟨⟨value, fits⟩⟩
  · rintro ⟨⟨value, fits⟩⟩
    obtain ⟨box, box_mem, represents⟩ := (valid neighbours).mp ⟨value, fits⟩
    exact ⟨box, Finset.mem_filter.mpr ⟨box_mem, represents⟩⟩

theorem sum_pos_iff_exists {index_type : Type} [Fintype index_type]
    (values : index_type → ℕ) : 0 < ∑ index, values index ↔ ∃ index, 0 < values index := by
  rw [Nat.pos_iff_ne_zero, Ne, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall]
  exact exists_congr fun _ => Nat.pos_iff_ne_zero.symm

theorem reconstructed_count_pos_iff (h_hidden : originals h = false)
    (table : Finset (neighbour_box csp h)) (valid : is_valid_cc_table csp h table)
    (tuple : original_tuple csp originals) :
    0 < reconstructed_extension_count csp originals h table tuple ↔
      0 < extension_count csp originals tuple := by
  rw [reconstructed_count_eq_sum, extension_count_eq_sum csp originals h h_hidden,
    sum_pos_iff_exists, sum_pos_iff_exists]
  exact exists_congr fun rest => box_count_pos_iff csp h table valid _

theorem reconstructed_count_le_of_pointwise (h_hidden : originals h = false)
    (table : Finset (neighbour_box csp h))
    (pointwise : ∀ neighbours, box_count csp h table neighbours ≤ old_value_count csp h neighbours)
    (tuple : original_tuple csp originals) :
    reconstructed_extension_count csp originals h table tuple ≤
      extension_count csp originals tuple := by
  rw [reconstructed_count_eq_sum, extension_count_eq_sum csp originals h h_hidden]
  exact Finset.sum_le_sum fun rest _ => pointwise _

theorem reconstructed_count_of_unique_extension (h_hidden : originals h = false)
    (table : Finset (neighbour_box csp h)) (valid : is_valid_cc_table csp h table)
    (unique : has_unique_extension csp originals) (candidate : assignment csp)
    (solution : is_solution csp candidate) :
    reconstructed_extension_count csp originals h table
        (restrict_to_originals csp originals candidate) =
      box_count csp h table
        (neighbour_tuple_of_rest csp h (rest_of_assignment csp h candidate)) := by
  rw [reconstructed_count_eq_sum]
  let center : {rest : rest_assignment csp h // rest_is_consistent csp h rest ∧
      rest_encodes_tuple csp originals h rest (restrict_to_originals csp originals candidate)} :=
    ⟨rest_of_assignment csp h candidate, rest_of_solution_consistent csp h candidate solution,
      rest_of_extension_encodes csp originals h candidate _ rfl⟩
  rw [Finset.sum_eq_single center]
  · intro other _ other_ne
    by_contra not_zero
    have positive := (box_count_pos_iff csp h table valid _).mp (Nat.pos_of_ne_zero not_zero)
    obtain ⟨⟨value, fits⟩⟩ := Fintype.card_pos_iff.mp positive
    have other_solution := assemble_is_solution csp h other.val value other.property.1 fits
    have other_restricts := assemble_restricts csp originals h h_hidden other.val value _
      other.property.2
    have count_one := unique _ ⟨candidate, solution, rfl⟩
    obtain ⟨only, _, only_unique⟩ := (extension_count_eq_one_iff csp originals _).mp count_one
    have same : assemble csp h other.val value = candidate :=
      (only_unique _ ⟨other_solution, other_restricts⟩).trans
        (only_unique candidate ⟨solution, rfl⟩).symm
    apply other_ne
    apply Subtype.ext
    show other.val = rest_of_assignment csp h candidate
    exact (rest_of_assemble csp h other.val value).symm.trans
      (congrArg (rest_of_assignment csp h) same)
  · intro not_mem
    exact absurd (Finset.mem_univ center) not_mem

theorem reconstructed_unique_iff (h_hidden : originals h = false)
    (table : Finset (neighbour_box csp h)) (valid : is_valid_cc_table csp h table)
    (unique : has_unique_extension csp originals) :
    (∀ tuple, in_relation csp originals tuple →
      reconstructed_extension_count csp originals h table tuple = 1) ↔
    ∀ candidate, is_solution csp candidate →
      box_count csp h table
        (neighbour_tuple_of_rest csp h (rest_of_assignment csp h candidate)) = 1 := by
  constructor
  · intro all_one candidate solution
    rw [← reconstructed_count_of_unique_extension csp originals h h_hidden table valid unique
      candidate solution]
    exact all_one _ ⟨candidate, solution, rfl⟩
  · rintro all_one tuple ⟨candidate, solution, rfl⟩
    rw [reconstructed_count_of_unique_extension csp originals h h_hidden table valid unique
      candidate solution]
    exact all_one candidate solution

end decomposition

section construction

variable (csp : binary_csp vertex_count) (h : Fin vertex_count)

theorem agree_outside_refl (pivot : neighbour_vertex csp h) (box : neighbour_box csp h) :
    agree_outside csp h pivot box box := fun _ _ => rfl

theorem agree_outside_symm (pivot : neighbour_vertex csp h) (first second : neighbour_box csp h)
    (agree : agree_outside csp h pivot first second) : agree_outside csp h pivot second first :=
  fun y y_ne => (agree y y_ne).symm

theorem agree_outside_trans (pivot : neighbour_vertex csp h)
    (first second third : neighbour_box csp h) (first_second : agree_outside csp h pivot first second)
    (second_third : agree_outside csp h pivot second third) :
    agree_outside csp h pivot first third :=
  fun y y_ne => (first_second y y_ne).trans (second_third y y_ne)

theorem agree_outside_equivalence (pivot : neighbour_vertex csp h) :
    Equivalence (agree_outside csp h pivot) :=
  ⟨agree_outside_refl csp h pivot, fun agree => agree_outside_symm csp h pivot _ _ agree,
    fun first_second second_third =>
      agree_outside_trans csp h pivot _ _ _ first_second second_third⟩

theorem merged_box_represents_iff (table : Finset (neighbour_box csp h))
    (pivot : neighbour_vertex csp h) (box : neighbour_box csp h) (neighbours : neighbour_tuple csp h) :
    box_represents csp h (merged_box csp h table pivot box) neighbours ↔
      ∃ other ∈ table.filter (agree_outside csp h pivot box),
        box_represents csp h other neighbours := by
  constructor
  · intro represents
    have at_pivot := represents pivot
    unfold merged_box at at_pivot
    rw [Function.update_self, Finset.mem_biUnion] at at_pivot
    obtain ⟨other, other_mem, in_other⟩ := at_pivot
    refine ⟨other, other_mem, fun y => ?_⟩
    by_cases y_is_pivot : y = pivot
    · subst y
      exact in_other
    · have agree := (Finset.mem_filter.mp other_mem).2
      have at_y := represents y
      unfold merged_box at at_y
      rw [Function.update_of_ne y_is_pivot] at at_y
      rw [← agree y y_is_pivot]
      exact at_y
  · rintro ⟨other, other_mem, other_represents⟩ y
    unfold merged_box
    by_cases y_is_pivot : y = pivot
    · subst y
      rw [Function.update_self, Finset.mem_biUnion]
      exact ⟨other, other_mem, other_represents _⟩
    · rw [Function.update_of_ne y_is_pivot, (Finset.mem_filter.mp other_mem).2 y y_is_pivot]
      exact other_represents y

theorem merged_box_eq_of_agree (table : Finset (neighbour_box csp h))
    (pivot : neighbour_vertex csp h) (first second : neighbour_box csp h)
    (agree : agree_outside csp h pivot first second) :
    merged_box csp h table pivot first = merged_box csp h table pivot second := by
  have same_class : table.filter (agree_outside csp h pivot first) =
      table.filter (agree_outside csp h pivot second) := by
    ext other
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨other_mem, agree_first⟩
      exact ⟨other_mem, agree_outside_trans csp h pivot _ _ _
        (agree_outside_symm csp h pivot _ _ agree) agree_first⟩
    · rintro ⟨other_mem, agree_second⟩
      exact ⟨other_mem, agree_outside_trans csp h pivot _ _ _ agree agree_second⟩
  funext y
  unfold merged_box
  rw [same_class]
  by_cases y_is_pivot : y = pivot
  · subst y
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne y_is_pivot, Function.update_of_ne y_is_pivot]
    exact agree y y_is_pivot

theorem merge_table_filter_eq (table : Finset (neighbour_box csp h))
    (pivot : neighbour_vertex csp h) (neighbours : neighbour_tuple csp h) :
    (merge_table csp h table pivot).filter (fun box => box_represents csp h box neighbours) =
      (table.filter fun box => box_represents csp h box neighbours).image
        (merged_box csp h table pivot) := by
  ext merged
  simp only [merge_table, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨box, box_mem, rfl⟩, represents⟩
    obtain ⟨other, other_mem, other_represents⟩ :=
      (merged_box_represents_iff csp h table pivot box neighbours).mp represents
    have other_in := Finset.mem_filter.mp other_mem
    exact ⟨other, ⟨other_in.1, other_represents⟩,
      (merged_box_eq_of_agree csp h table pivot box other other_in.2).symm⟩
  · rintro ⟨box, ⟨box_mem, represents⟩, rfl⟩
    exact ⟨⟨box, box_mem, rfl⟩, (merged_box_represents_iff csp h table pivot box neighbours).mpr
      ⟨box, Finset.mem_filter.mpr ⟨box_mem, agree_outside_refl csp h pivot box⟩, represents⟩⟩

theorem merge_count_le (table : Finset (neighbour_box csp h)) (pivot : neighbour_vertex csp h)
    (neighbours : neighbour_tuple csp h) :
    box_count csp h (merge_table csp h table pivot) neighbours ≤
      box_count csp h table neighbours := by
  unfold box_count
  rw [merge_table_filter_eq]
  exact Finset.card_image_le

theorem merge_represents_iff (table : Finset (neighbour_box csp h))
    (pivot : neighbour_vertex csp h) (neighbours : neighbour_tuple csp h) :
    (∃ box ∈ merge_table csp h table pivot, box_represents csp h box neighbours) ↔
      ∃ box ∈ table, box_represents csp h box neighbours := by
  have filter_eq := merge_table_filter_eq csp h table pivot neighbours
  constructor
  · rintro ⟨box, box_mem, represents⟩
    have in_filter : box ∈ (merge_table csp h table pivot).filter
        (fun box => box_represents csp h box neighbours) :=
      Finset.mem_filter.mpr ⟨box_mem, represents⟩
    rw [filter_eq, Finset.mem_image] at in_filter
    obtain ⟨original, original_mem, _⟩ := in_filter
    exact ⟨original, (Finset.mem_filter.mp original_mem).1, (Finset.mem_filter.mp original_mem).2⟩
  · rintro ⟨box, box_mem, represents⟩
    have in_filter : merged_box csp h table pivot box ∈ (merge_table csp h table pivot).filter
        (fun box => box_represents csp h box neighbours) := by
      rw [filter_eq]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨box_mem, represents⟩)
    exact ⟨_, (Finset.mem_filter.mp in_filter).1, (Finset.mem_filter.mp in_filter).2⟩

theorem merge_along_cons (start : Finset (neighbour_box csp h)) (pivot : neighbour_vertex csp h)
    (pivots : List (neighbour_vertex csp h)) :
    merge_along csp h start (pivot :: pivots) =
      merge_along csp h (merge_table csp h start pivot) pivots := rfl

theorem merge_along_count_le (pivots : List (neighbour_vertex csp h))
    (start : Finset (neighbour_box csp h)) (neighbours : neighbour_tuple csp h) :
    box_count csp h (merge_along csp h start pivots) neighbours ≤
      box_count csp h start neighbours := by
  induction pivots generalizing start with
  | nil => exact le_refl _
  | cons pivot rest induction_step =>
    rw [merge_along_cons]
    exact (induction_step _).trans (merge_count_le csp h start pivot neighbours)

theorem merge_along_valid (pivots : List (neighbour_vertex csp h))
    (start : Finset (neighbour_box csp h)) (valid : is_valid_cc_table csp h start) :
    is_valid_cc_table csp h (merge_along csp h start pivots) := by
  induction pivots generalizing start with
  | nil => exact valid
  | cons pivot rest induction_step =>
    rw [merge_along_cons]
    apply induction_step
    intro neighbours
    rw [merge_represents_iff]
    exact valid neighbours

theorem box_of_value_represents_iff (value : Fin (csp.domain_size h))
    (neighbours : neighbour_tuple csp h) :
    box_represents csp h (box_of_value csp h value) neighbours ↔
      value_fits_neighbours csp h value neighbours := by
  unfold box_represents box_of_value value_fits_neighbours
  simp

theorem value_table_filter_eq (neighbours : neighbour_tuple csp h) :
    (value_table csp h).filter (fun box => box_represents csp h box neighbours) =
      (Finset.univ.filter fun value => value_fits_neighbours csp h value neighbours).image
        (box_of_value csp h) := by
  ext box
  simp only [value_table, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨value, rfl⟩, represents⟩
    exact ⟨value, (box_of_value_represents_iff csp h value neighbours).mp represents, rfl⟩
  · rintro ⟨value, fits, rfl⟩
    exact ⟨⟨value, rfl⟩, (box_of_value_represents_iff csp h value neighbours).mpr fits⟩

theorem value_table_count_le (neighbours : neighbour_tuple csp h) :
    box_count csp h (value_table csp h) neighbours ≤ old_value_count csp h neighbours := by
  unfold box_count old_value_count
  rw [value_table_filter_eq, Fintype.card_subtype]
  exact Finset.card_image_le

theorem value_table_valid : is_valid_cc_table csp h (value_table csp h) := by
  intro neighbours
  constructor
  · rintro ⟨value, fits⟩
    exact ⟨box_of_value csp h value, Finset.mem_image_of_mem _ (Finset.mem_univ value),
      (box_of_value_represents_iff csp h value neighbours).mpr fits⟩
  · rintro ⟨box, box_mem, represents⟩
    obtain ⟨value, _, rfl⟩ := Finset.mem_image.mp box_mem
    exact ⟨value, (box_of_value_represents_iff csp h value neighbours).mp represents⟩

theorem box_of_tuple_represents_iff (center neighbours : neighbour_tuple csp h) :
    box_represents csp h (box_of_tuple csp h center) neighbours ↔ neighbours = center := by
  unfold box_represents box_of_tuple
  simp only [Finset.mem_singleton]
  exact ⟨fun same => funext same, fun same y => by rw [same]⟩

theorem tuple_table_count_le (neighbours : neighbour_tuple csp h) :
    box_count csp h (tuple_table csp h) neighbours ≤ old_value_count csp h neighbours := by
  unfold box_count
  by_cases fits_exists : ∃ value, value_fits_neighbours csp h value neighbours
  · have subset : (tuple_table csp h).filter (fun box => box_represents csp h box neighbours) ⊆
        {box_of_tuple csp h neighbours} := by
      intro box box_mem
      obtain ⟨table_mem, represents⟩ := Finset.mem_filter.mp box_mem
      obtain ⟨center, _, rfl⟩ := Finset.mem_image.mp table_mem
      rw [Finset.mem_singleton, (box_of_tuple_represents_iff csp h center neighbours).mp represents]
    have one_le : 1 ≤ old_value_count csp h neighbours := by
      obtain ⟨value, fits⟩ := fits_exists
      exact Fintype.card_pos_iff.mpr ⟨⟨value, fits⟩⟩
    exact (Finset.card_le_card subset).trans (by rw [Finset.card_singleton]; exact one_le)
  · have empty : (tuple_table csp h).filter (fun box => box_represents csp h box neighbours) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro box table_mem represents
      obtain ⟨center, center_mem, rfl⟩ := Finset.mem_image.mp table_mem
      have same := (box_of_tuple_represents_iff csp h center neighbours).mp represents
      rw [Finset.mem_filter] at center_mem
      rw [← same] at center_mem
      exact fits_exists center_mem.2
    rw [empty, Finset.card_empty]
    exact Nat.zero_le _

theorem tuple_table_valid : is_valid_cc_table csp h (tuple_table csp h) := by
  intro neighbours
  constructor
  · intro fits_exists
    exact ⟨box_of_tuple csp h neighbours, Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fits_exists⟩),
      (box_of_tuple_represents_iff csp h neighbours neighbours).mpr rfl⟩
  · rintro ⟨box, box_mem, represents⟩
    obtain ⟨center, center_mem, rfl⟩ := Finset.mem_image.mp box_mem
    have same := (box_of_tuple_represents_iff csp h center neighbours).mp represents
    rw [Finset.mem_filter] at center_mem
    rw [same]
    exact center_mem.2

def construction_start (from_values : Bool) (first_pivot : neighbour_vertex csp h) :
    Finset (neighbour_box csp h) :=
  if from_values then value_table csp h else merge_table csp h (tuple_table csp h) first_pivot

theorem construction_start_count_le (from_values : Bool) (first_pivot : neighbour_vertex csp h)
    (neighbours : neighbour_tuple csp h) :
    box_count csp h (construction_start csp h from_values first_pivot) neighbours ≤
      old_value_count csp h neighbours := by
  unfold construction_start
  cases from_values
  · exact (merge_count_le csp h _ first_pivot neighbours).trans
      (tuple_table_count_le csp h neighbours)
  · exact value_table_count_le csp h neighbours

theorem construction_start_valid (from_values : Bool) (first_pivot : neighbour_vertex csp h) :
    is_valid_cc_table csp h (construction_start csp h from_values first_pivot) := by
  cases from_values
  · show is_valid_cc_table csp h (merge_table csp h (tuple_table csp h) first_pivot)
    intro neighbours
    rw [merge_represents_iff]
    exact tuple_table_valid csp h neighbours
  · exact value_table_valid csp h

theorem construction_cannot_increase (originals : Fin vertex_count → Bool)
    (h_hidden : originals h = false) (from_values : Bool) (first_pivot : neighbour_vertex csp h)
    (pivots : List (neighbour_vertex csp h)) (tuple : original_tuple csp originals) :
    reconstructed_extension_count csp originals h
        (merge_along csp h (construction_start csp h from_values first_pivot) pivots) tuple ≤
      extension_count csp originals tuple :=
  reconstructed_count_le_of_pointwise csp originals h h_hidden _
    (fun neighbours => (merge_along_count_le csp h pivots _ neighbours).trans
      (construction_start_count_le csp h from_values first_pivot neighbours)) tuple

theorem construction_keeps_unique_extension (originals : Fin vertex_count → Bool)
    (h_hidden : originals h = false) (from_values : Bool) (first_pivot : neighbour_vertex csp h)
    (pivots : List (neighbour_vertex csp h)) (unique : has_unique_extension csp originals)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple) :
    reconstructed_extension_count csp originals h
      (merge_along csp h (construction_start csp h from_values first_pivot) pivots) tuple = 1 := by
  have at_most := construction_cannot_increase csp h originals h_hidden from_values first_pivot
    pivots tuple
  rw [unique tuple in_rel] at at_most
  have valid := merge_along_valid csp h pivots _ (construction_start_valid csp h from_values first_pivot)
  have positive := (reconstructed_count_pos_iff csp originals h h_hidden _ valid tuple).mpr
    (by rw [unique tuple in_rel]; exact Nat.one_pos)
  omega

end construction

theorem reduction_steps_keep_unique_extension {tuple_type : Type}
    (counts : ℕ → tuple_type → ℕ) (step_count : ℕ)
    (never_increase : ∀ step < step_count, ∀ tuple, counts (step + 1) tuple ≤ counts step tuple)
    (never_lose : ∀ step < step_count, ∀ tuple, 0 < counts step tuple → 0 < counts (step + 1) tuple)
    (initially_unique : ∀ tuple, counts 0 tuple ≤ 1) :
    ∀ tuple, counts step_count tuple ≤ 1 ∧ (0 < counts 0 tuple → 0 < counts step_count tuple) := by
  induction step_count with
  | zero => exact fun tuple => ⟨initially_unique tuple, id⟩
  | succ step induction_step =>
    intro tuple
    obtain ⟨at_most, kept⟩ := induction_step
      (fun earlier earlier_lt => never_increase earlier (by omega))
      (fun earlier earlier_lt => never_lose earlier (by omega)) tuple
    exact ⟨(never_increase step (by omega) tuple).trans at_most,
      fun positive => never_lose step (by omega) tuple (kept positive)⟩

end parsimony
