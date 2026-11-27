import parsimony.minimal_support_counting
import parsimony.reduction_examples

namespace parsimony

section grouping

variable {vertex_count : ℕ}

structure is_grouping (old_csp new_csp : binary_csp vertex_count) (h pivot : Fin vertex_count)
    (group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)) : Prop where
  same_adjacent : ∀ x y, new_csp.adjacent x y = old_csp.adjacent x y
  same_size : ∀ x, x ≠ h → new_csp.domain_size x = old_csp.domain_size x
  same_allowed : ∀ x y, x ≠ h → y ≠ h → ∀ (a : Fin (old_csp.domain_size x))
    (b : Fin (old_csp.domain_size y)), new_csp.allowed x y a b = old_csp.allowed x y a b
  group_onto : ∀ j, ∃ i, group_of i = j
  group_allowed : ∀ y, old_csp.adjacent h y = true → ∀ (j : Fin (new_csp.domain_size h))
    (b : Fin (old_csp.domain_size y)),
    new_csp.allowed h y j b = true ↔ ∃ i, group_of i = j ∧ old_csp.allowed h y i b = true
  agree_outside_pivot : ∀ y, old_csp.adjacent h y = true → y ≠ pivot → ∀ i k,
    group_of i = group_of k → ∀ b : Fin (old_csp.domain_size y),
    old_csp.allowed h y i b = old_csp.allowed h y k b

def transported_selection (old_csp new_csp : binary_csp vertex_count)
    (new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool) :
    ∀ x : Fin vertex_count, Fin (old_csp.domain_size x) → Bool :=
  fun x a => if lt : a.val < new_csp.domain_size x then new_selected x ⟨a.val, lt⟩ else false

def is_compatible_member (old_csp new_csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (h : Fin vertex_count)
    (new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool)
    (i : Fin (old_csp.domain_size h)) : Prop :=
  ∀ c, old_csp.adjacent h c = true → earlier_in order h c = true →
    ∃ b : Fin (old_csp.domain_size c), old_csp.allowed h c i b = true ∧
      transported_selection old_csp new_csp new_selected c b = true

instance (old_csp new_csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (h : Fin vertex_count)
    (new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool)
    (i : Fin (old_csp.domain_size h)) :
    Decidable (is_compatible_member old_csp new_csp order h new_selected i) := by
  unfold is_compatible_member
  infer_instance

def grouped_back_selection (old_csp new_csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (h : Fin vertex_count)
    (group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h))
    (new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool) :
    ∀ x : Fin vertex_count, Fin (old_csp.domain_size x) → Bool :=
  Function.update (transported_selection old_csp new_csp new_selected) h
    (fun i => new_selected h (group_of i) &&
      decide (is_compatible_member old_csp new_csp order h new_selected i))

theorem earlier_chain_ne (order : List (Fin vertex_count)) (x y z : Fin vertex_count)
    (first : earlier_in order x y = true) (second : earlier_in order y z = true) : x ≠ z := by
  intro same
  rw [same] at first
  unfold earlier_in at first second
  rw [decide_eq_true_eq] at first second
  omega

theorem transported_of_ne {old_csp new_csp : binary_csp vertex_count} {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    (new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool)
    (x : Fin vertex_count) (x_ne_h : x ≠ h) (a : Fin (old_csp.domain_size x)) :
    transported_selection old_csp new_csp new_selected x a =
      new_selected x ⟨a.val, by rw [grouping.same_size x x_ne_h]; exact a.isLt⟩ := by
  unfold transported_selection
  rw [dite_eq_left (by rw [grouping.same_size x x_ne_h]; exact a.isLt)]

theorem ne_center_of_adjacent (csp : binary_csp vertex_count) (h c : Fin vertex_count)
    (adjacent : csp.adjacent h c = true) : c ≠ h := by
  intro same
  rw [same, csp.adjacent_irrefl] at adjacent
  exact Bool.false_ne_true adjacent

theorem member_supported_at_child {old_csp new_csp : binary_csp vertex_count}
    {originals : Fin vertex_count → Bool} {order : List (Fin vertex_count)}
    {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    {new_tuple : original_tuple new_csp originals}
    {new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool}
    (new_selection : is_selection_over new_csp originals order new_tuple new_selected)
    (j : Fin (new_csp.domain_size h)) (j_selected : new_selected h j = true)
    (c : Fin vertex_count) (adjacent : old_csp.adjacent h c = true)
    (earlier : earlier_in order h c = true) (c_ne_pivot : c ≠ pivot)
    (i : Fin (old_csp.domain_size h)) (i_in : group_of i = j) :
    ∃ b : Fin (old_csp.domain_size c), old_csp.allowed h c i b = true ∧
      transported_selection old_csp new_csp new_selected c b = true := by
  have c_ne_h := ne_center_of_adjacent old_csp h c adjacent
  obtain ⟨new_b, new_allowed, new_b_selected⟩ := new_selection.2 h c
    (by rw [grouping.same_adjacent]; exact adjacent) earlier j j_selected
  let b : Fin (old_csp.domain_size c) :=
    ⟨new_b.val, by rw [← grouping.same_size c c_ne_h]; exact new_b.isLt⟩
  obtain ⟨member, member_in, member_allowed⟩ :=
    (grouping.group_allowed c adjacent j b).mp new_allowed
  refine ⟨b, ?_, ?_⟩
  · rw [grouping.agree_outside_pivot c adjacent c_ne_pivot i member (i_in.trans member_in.symm) b]
    exact member_allowed
  · rw [transported_of_ne grouping new_selected c c_ne_h b]
    exact new_b_selected

theorem every_member_compatible {old_csp new_csp : binary_csp vertex_count}
    {originals : Fin vertex_count → Bool} {order : List (Fin vertex_count)}
    {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    {new_tuple : original_tuple new_csp originals}
    {new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool}
    (new_selection : is_selection_over new_csp originals order new_tuple new_selected)
    (pivot_not_child : ¬ (old_csp.adjacent h pivot = true ∧ earlier_in order h pivot = true))
    (j : Fin (new_csp.domain_size h)) (j_selected : new_selected h j = true)
    (i : Fin (old_csp.domain_size h)) (i_in : group_of i = j) :
    is_compatible_member old_csp new_csp order h new_selected i := by
  intro c adjacent earlier
  have c_ne_pivot : c ≠ pivot := by
    intro same
    rw [same] at adjacent earlier
    exact pivot_not_child ⟨adjacent, earlier⟩
  exact member_supported_at_child grouping new_selection j j_selected c adjacent earlier c_ne_pivot
    i i_in

theorem pivot_member_compatible {old_csp new_csp : binary_csp vertex_count}
    {originals : Fin vertex_count → Bool} {order : List (Fin vertex_count)}
    {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    {new_tuple : original_tuple new_csp originals}
    {new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool}
    (new_selection : is_selection_over new_csp originals order new_tuple new_selected)
    (pivot_adjacent : old_csp.adjacent h pivot = true)
    (pivot_later : earlier_in order h pivot = true)
    (j : Fin (new_csp.domain_size h)) (j_selected : new_selected h j = true) :
    ∃ i, group_of i = j ∧ is_compatible_member old_csp new_csp order h new_selected i := by
  have pivot_ne_h := ne_center_of_adjacent old_csp h pivot pivot_adjacent
  obtain ⟨new_b, new_allowed, new_b_selected⟩ := new_selection.2 h pivot
    (by rw [grouping.same_adjacent]; exact pivot_adjacent) pivot_later j j_selected
  let b : Fin (old_csp.domain_size pivot) :=
    ⟨new_b.val, by rw [← grouping.same_size pivot pivot_ne_h]; exact new_b.isLt⟩
  obtain ⟨member, member_in, member_allowed⟩ :=
    (grouping.group_allowed pivot pivot_adjacent j b).mp new_allowed
  refine ⟨member, member_in, ?_⟩
  intro c adjacent earlier
  by_cases c_is_pivot : c = pivot
  · rw [c_is_pivot]
    refine ⟨b, member_allowed, ?_⟩
    rw [transported_of_ne grouping new_selected pivot pivot_ne_h b]
    exact new_b_selected
  · exact member_supported_at_child grouping new_selection j j_selected c adjacent earlier
      c_is_pivot member member_in

theorem grouped_back_is_selection {old_csp new_csp : binary_csp vertex_count}
    {originals : Fin vertex_count → Bool} {order : List (Fin vertex_count)}
    {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of) (h_hidden : originals h = false)
    (old_tuple : original_tuple old_csp originals) (new_tuple : original_tuple new_csp originals)
    (same_tuple : ∀ x, (new_tuple x).val = (old_tuple x).val)
    {new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool}
    (new_selection : is_selection_over new_csp originals order new_tuple new_selected) :
    is_selection_over old_csp originals order old_tuple
      (grouped_back_selection old_csp new_csp order h group_of new_selected) := by
  constructor
  · intro x on_x a
    have x_ne_h : x ≠ h := by
      intro same
      rw [same, h_hidden] at on_x
      exact Bool.false_ne_true on_x
    unfold grouped_back_selection
    rw [Function.update_of_ne x_ne_h, transported_of_ne grouping new_selected x x_ne_h a,
      new_selection.1 x on_x, decide_eq_decide, Fin.ext_iff, Fin.ext_iff, same_tuple]
  · intro x y adjacent earlier a a_selected
    by_cases x_is_h : x = h
    · subst x_is_h
      have y_ne_x := ne_center_of_adjacent old_csp x y adjacent
      unfold grouped_back_selection at a_selected
      rw [Function.update_self, Bool.and_eq_true, decide_eq_true_eq] at a_selected
      obtain ⟨b, allowed_b, b_selected⟩ := a_selected.2 y adjacent earlier
      refine ⟨b, allowed_b, ?_⟩
      unfold grouped_back_selection
      rw [Function.update_of_ne y_ne_x]
      exact b_selected
    · by_cases y_is_h : y = h
      · subst y_is_h
        have h_adjacent_x : old_csp.adjacent y x = true := by
          rw [old_csp.adjacent_symm]
          exact adjacent
        unfold grouped_back_selection at a_selected
        rw [Function.update_of_ne x_is_h, transported_of_ne grouping new_selected x x_is_h a]
          at a_selected
        obtain ⟨j, new_allowed, j_selected⟩ := new_selection.2 x y
          (by rw [grouping.same_adjacent]; exact adjacent) earlier _ a_selected
        rw [new_csp.allowed_symm] at new_allowed
        obtain ⟨first_member, first_in, first_allowed⟩ :=
          (grouping.group_allowed x h_adjacent_x j a).mp new_allowed
        have pick : ∃ i, group_of i = j ∧
            is_compatible_member old_csp new_csp order y new_selected i ∧
            old_csp.allowed y x i a = true := by
          by_cases pivot_child : old_csp.adjacent y pivot = true ∧ earlier_in order y pivot = true
          · obtain ⟨member, member_in, member_compatible⟩ := pivot_member_compatible grouping
              new_selection pivot_child.1 pivot_child.2 j j_selected
            have x_ne_pivot := earlier_chain_ne order x y pivot earlier pivot_child.2
            refine ⟨member, member_in, member_compatible, ?_⟩
            rw [grouping.agree_outside_pivot x h_adjacent_x x_ne_pivot member first_member
              (member_in.trans first_in.symm) a]
            exact first_allowed
          · exact ⟨first_member, first_in, every_member_compatible grouping new_selection
              pivot_child j j_selected first_member first_in, first_allowed⟩
        obtain ⟨member, member_in, member_compatible, member_allowed⟩ := pick
        refine ⟨member, ?_, ?_⟩
        · rw [old_csp.allowed_symm]
          exact member_allowed
        · unfold grouped_back_selection
          rw [Function.update_self, member_in, j_selected, Bool.true_and, decide_eq_true_eq]
          exact member_compatible
      · unfold grouped_back_selection at a_selected
        rw [Function.update_of_ne x_is_h, transported_of_ne grouping new_selected x x_is_h a]
          at a_selected
        obtain ⟨new_b, new_allowed, new_b_selected⟩ := new_selection.2 x y
          (by rw [grouping.same_adjacent]; exact adjacent) earlier _ a_selected
        let b : Fin (old_csp.domain_size y) :=
          ⟨new_b.val, by rw [← grouping.same_size y y_is_h]; exact new_b.isLt⟩
        refine ⟨b, ?_, ?_⟩
        · rw [← grouping.same_allowed x y x_is_h y_is_h a b]
          exact new_allowed
        · unfold grouped_back_selection
          rw [Function.update_of_ne y_is_h, transported_of_ne grouping new_selected y y_is_h b]
          exact new_b_selected

theorem compatible_member_exists {old_csp new_csp : binary_csp vertex_count}
    {originals : Fin vertex_count → Bool} {order : List (Fin vertex_count)}
    {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    {new_tuple : original_tuple new_csp originals}
    {new_selected : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool}
    (new_selection : is_selection_over new_csp originals order new_tuple new_selected)
    (j : Fin (new_csp.domain_size h)) (j_selected : new_selected h j = true) :
    ∃ i, group_of i = j ∧ is_compatible_member old_csp new_csp order h new_selected i := by
  by_cases pivot_child : old_csp.adjacent h pivot = true ∧ earlier_in order h pivot = true
  · exact pivot_member_compatible grouping new_selection pivot_child.1 pivot_child.2 j j_selected
  · obtain ⟨member, member_in⟩ := grouping.group_onto j
    exact ⟨member, member_in, every_member_compatible grouping new_selection pivot_child j
      j_selected member member_in⟩

theorem compatible_member_congr {old_csp new_csp : binary_csp vertex_count}
    {order : List (Fin vertex_count)} {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    (first second : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool)
    (same_off_center : ∀ x, x ≠ h → ∀ b, first x b = second x b)
    (i : Fin (old_csp.domain_size h)) :
    is_compatible_member old_csp new_csp order h first i →
      is_compatible_member old_csp new_csp order h second i := by
  intro compatible c adjacent earlier
  have c_ne_h := ne_center_of_adjacent old_csp h c adjacent
  obtain ⟨b, allowed_b, b_selected⟩ := compatible c adjacent earlier
  refine ⟨b, allowed_b, ?_⟩
  rw [transported_of_ne grouping second c c_ne_h b, ← same_off_center c c_ne_h,
    ← transported_of_ne grouping first c c_ne_h b]
  exact b_selected

theorem grouped_back_injective {old_csp new_csp : binary_csp vertex_count}
    {originals : Fin vertex_count → Bool} {order : List (Fin vertex_count)}
    {h pivot : Fin vertex_count}
    {group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h)}
    (grouping : is_grouping old_csp new_csp h pivot group_of)
    {new_tuple : original_tuple new_csp originals}
    {first second : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool}
    (first_selection : is_selection_over new_csp originals order new_tuple first)
    (second_selection : is_selection_over new_csp originals order new_tuple second)
    (same_back : grouped_back_selection old_csp new_csp order h group_of first =
      grouped_back_selection old_csp new_csp order h group_of second) :
    first = second := by
  have same_off_center : ∀ x, x ≠ h → ∀ b, first x b = second x b := by
    intro x x_ne_h b
    let a : Fin (old_csp.domain_size x) :=
      ⟨b.val, by rw [← grouping.same_size x x_ne_h]; exact b.isLt⟩
    have at_a := congrFun (congrFun same_back x) a
    unfold grouped_back_selection at at_a
    rw [Function.update_of_ne x_ne_h, Function.update_of_ne x_ne_h,
      transported_of_ne grouping first x x_ne_h a, transported_of_ne grouping second x x_ne_h a]
      at at_a
    exact at_a
  have one_way : ∀ one other : ∀ x : Fin vertex_count, Fin (new_csp.domain_size x) → Bool,
      is_selection_over new_csp originals order new_tuple one →
      grouped_back_selection old_csp new_csp order h group_of one =
        grouped_back_selection old_csp new_csp order h group_of other →
      (∀ x, x ≠ h → ∀ b, one x b = other x b) →
      ∀ j, one h j = true → other h j = true := by
    intro one other one_selection same off j j_selected
    obtain ⟨member, member_in, member_compatible⟩ :=
      compatible_member_exists grouping one_selection j j_selected
    have other_compatible := compatible_member_congr grouping one other off member
      member_compatible
    have at_member := congrFun (congrFun same h) member
    unfold grouped_back_selection at at_member
    rw [Function.update_self, Function.update_self, member_in, j_selected, Bool.true_and,
      decide_eq_true member_compatible, decide_eq_true other_compatible, Bool.and_true]
      at at_member
    exact at_member.symm
  funext x b
  by_cases x_is_h : x = h
  · subst x_is_h
    rw [Bool.eq_iff_iff]
    exact ⟨one_way first second first_selection same_back same_off_center b,
      one_way second first second_selection same_back.symm
        (fun y y_ne b => (same_off_center y y_ne b).symm) b⟩
  · exact same_off_center x x_is_h b

theorem grouping_minimal_support_count_le (old_csp new_csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (h pivot : Fin vertex_count)
    (group_of : Fin (old_csp.domain_size h) → Fin (new_csp.domain_size h))
    (grouping : is_grouping old_csp new_csp h pivot group_of) (h_hidden : originals h = false)
    (old_tuple : original_tuple old_csp originals) (new_tuple : original_tuple new_csp originals)
    (same_tuple : ∀ x, (new_tuple x).val = (old_tuple x).val) :
    models_over_tuple new_csp originals originals (minimal_support_encoding new_csp originals order)
        new_tuple ≤
      models_over_tuple old_csp originals originals
        (minimal_support_encoding old_csp originals order) old_tuple := by
  classical
  rw [minimal_support_models_over_tuple_eq_selection_count,
    minimal_support_models_over_tuple_eq_selection_count]
  exact Fintype.card_le_of_injective
    (fun selection => ⟨grouped_back_selection old_csp new_csp order h group_of selection.val,
      grouped_back_is_selection grouping h_hidden old_tuple new_tuple same_tuple
        selection.property⟩)
    (fun first second same => Subtype.ext (grouped_back_injective grouping first.property
      second.property (congrArg Subtype.val same)))

end grouping

namespace counterexamples

def grouped_partition_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 2] [(0, 1, [(0, 0), (1, 0), (0, 1), (1, 1)]), (1, 2, [(0, 0), (1, 1)])]
    (by decide) (by decide)

def partition_group_of :
    Fin (rule_four_partition_old_csp.domain_size 1) → Fin (grouped_partition_csp.domain_size 1) :=
  fun i => if i.val = 0 then ⟨0, by decide +kernel⟩ else ⟨1, by decide +kernel⟩

theorem grouped_partition_is_grouping :
    is_grouping rule_four_partition_old_csp grouped_partition_csp 1 0 partition_group_of where
  same_adjacent := by decide +kernel
  same_size := by decide +kernel
  same_allowed := by decide +kernel
  group_onto := by decide +kernel
  group_allowed := by decide +kernel
  agree_outside_pivot := by decide +kernel

theorem grouped_partition_counts :
    model_count (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden
        [0, 1, 2]) = 6 ∧
      model_count (minimal_support_encoding grouped_partition_csp middle_vertex_is_hidden
        [0, 1, 2]) = 4 ∧
      relation_count grouped_partition_csp middle_vertex_is_hidden = 4 ∧
      models_over_tuple grouped_partition_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding grouped_partition_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values grouped_partition_csp middle_vertex_is_hidden ![0, 0, 1]) = 1 ∧
      models_over_tuple rule_four_partition_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_old_csp middle_vertex_is_hidden ![0, 0, 1]) = 2 := by
  decide +kernel

theorem grouped_partition_count_le :
    models_over_tuple grouped_partition_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding grouped_partition_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values grouped_partition_csp middle_vertex_is_hidden ![0, 0, 1]) ≤
      models_over_tuple rule_four_partition_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_old_csp middle_vertex_is_hidden ![0, 0, 1]) :=
  grouping_minimal_support_count_le rule_four_partition_old_csp grouped_partition_csp
    middle_vertex_is_hidden [0, 1, 2] 1 0 partition_group_of grouped_partition_is_grouping
    (by decide) _ _ (by decide +kernel)

end counterexamples

end parsimony
