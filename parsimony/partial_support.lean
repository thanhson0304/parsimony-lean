import parsimony.bijection
import parsimony.descent
import parsimony.rooted_orders

namespace parsimony

variable {vertex_count : ℕ}

theorem partial_support_model_extends (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (partial_support_encoding csp originals))
    (x : Fin vertex_count) (a : Fin (csp.domain_size x))
    (a_selected : valuation (Sum.inl ⟨x, a⟩) = true) :
    ∃ candidate : assignment csp, is_solution csp candidate ∧ candidate x = a ∧
      ∀ y, valuation (Sum.inl ⟨y, candidate y⟩) = true := by
  obtain ⟨_, edges⟩ := (is_model_partial_support_iff csp originals valuation).mp model
  obtain ⟨order, tree_order, x_first⟩ := exists_tree_order_with_root csp tree x
  obtain ⟨candidate, candidate_x, all_selected, solution⟩ := exists_solution_by_descent csp order
    tree_order (fun y b => valuation (Sum.inl ⟨y, b⟩) = true) x x_first a a_selected
    (fun p q adjacent_p_q _ b b_selected => edges p q adjacent_p_q b b_selected)
  exact ⟨candidate, solution, candidate_x, all_selected⟩

theorem selected_candidate_restricts (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (tuple : original_tuple csp originals)
    (encodes : encodes_tuple csp originals ladder_on valuation tuple)
    (candidate : assignment csp)
    (all_selected : ∀ y, valuation (Sum.inl ⟨y, candidate y⟩) = true) :
    restrict_to_originals csp originals candidate = tuple := by
  funext x
  have selected := all_selected x.val
  rw [encodes x (candidate x.val)] at selected
  exact of_decide_eq_true selected

theorem partial_support_model_has_selected_extension (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true)
    (valuation : boolean_variable csp originals → Bool)
    (model : is_model valuation (partial_support_encoding csp originals))
    (tuple : original_tuple csp originals)
    (encodes : encodes_tuple csp originals originals valuation tuple) :
    ∃ candidate : assignment csp, is_solution csp candidate ∧
      restrict_to_originals csp originals candidate = tuple ∧
      ∀ y, valuation (Sum.inl ⟨y, candidate y⟩) = true := by
  obtain ⟨r, r_on⟩ := has_original
  have root_selected : valuation (Sum.inl ⟨r, tuple ⟨r, r_on⟩⟩) = true := by
    rw [encodes ⟨r, r_on⟩ (tuple ⟨r, r_on⟩)]
    simp
  obtain ⟨candidate, solution, _, all_selected⟩ := partial_support_model_extends csp originals tree
    valuation model r (tuple ⟨r, r_on⟩) root_selected
  exact ⟨candidate, solution,
    selected_candidate_restricts csp originals originals valuation tuple encodes candidate
      all_selected, all_selected⟩

theorem valuation_of_solution_is_partial_support_model (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (candidate : assignment csp)
    (solution : is_solution csp candidate) :
    is_model (valuation_of_assignment csp originals candidate)
      (partial_support_encoding csp originals) :=
  (is_model_partial_support_iff csp originals _).mpr
    ⟨fun x on_x => ⟨candidate x, valuation_of_assignment_block csp originals candidate x on_x⟩,
      fun x y adjacent_x_y =>
        valuation_of_solution_edge csp originals candidate solution x y adjacent_x_y⟩

theorem partial_support_is_projection_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) :
    is_projection_exact csp originals originals (partial_support_encoding csp originals) := by
  constructor
  · intro valuation model
    obtain ⟨blocks, _⟩ := (is_model_partial_support_iff csp originals valuation).mp model
    choose tuple tuple_fixed using fun x : original_vertex originals => blocks x.val x.property
    have encodes : encodes_tuple csp originals originals valuation tuple :=
      fun x a => (tuple_fixed x).1 a
    obtain ⟨candidate, solution, restricted, _⟩ := partial_support_model_has_selected_extension csp
      originals tree has_original valuation model tuple encodes
    exact ⟨tuple, ⟨candidate, solution, restricted⟩, encodes⟩
  · rintro tuple ⟨candidate, solution, restricted⟩
    subst restricted
    exact ⟨valuation_of_assignment csp originals candidate,
      valuation_of_solution_is_partial_support_model csp originals candidate solution,
      valuation_of_assignment_encodes csp originals originals candidate⟩

theorem partial_support_unique_model_of_unique_extension (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) (tuple : original_tuple csp originals)
    (unique_extension : ∃! candidate, is_solution csp candidate ∧
      restrict_to_originals csp originals candidate = tuple) :
    ∃! valuation, is_model valuation (partial_support_encoding csp originals) ∧
      encodes_tuple csp originals originals valuation tuple := by
  obtain ⟨candidate, ⟨solution, restricted⟩, only_candidate⟩ := unique_extension
  have candidate_encodes : encodes_tuple csp originals originals
      (valuation_of_assignment csp originals candidate) tuple := by
    rw [← restricted]
    exact valuation_of_assignment_encodes csp originals originals candidate
  refine ⟨valuation_of_assignment csp originals candidate,
    ⟨valuation_of_solution_is_partial_support_model csp originals candidate solution,
      candidate_encodes⟩, ?_⟩
  rintro other ⟨other_model, other_encodes⟩
  obtain ⟨blocks, _⟩ := (is_model_partial_support_iff csp originals other).mp other_model
  funext variable_name
  rcases variable_name with ⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩
  · show other (Sum.inl ⟨x, a⟩) = decide (a = candidate x)
    cases other_value : other (Sum.inl ⟨x, a⟩) with
    | true =>
      obtain ⟨extension, extension_solution, extension_x, extension_selected⟩ :=
        partial_support_model_extends csp originals tree other other_model x a other_value
      have extension_restricted := selected_candidate_restricts csp originals originals other tuple
        other_encodes extension extension_selected
      have extension_is_candidate := only_candidate extension
        ⟨extension_solution, extension_restricted⟩
      subst extension_is_candidate
      subst extension_x
      simp
    | false =>
      obtain ⟨extension, extension_solution, extension_restricted, extension_selected⟩ :=
        partial_support_model_has_selected_extension csp originals tree has_original other
          other_model tuple other_encodes
      have extension_is_candidate := only_candidate extension
        ⟨extension_solution, extension_restricted⟩
      subst extension_is_candidate
      have not_extension : a ≠ extension x := by
        intro a_is_extension
        have at_x := extension_selected x
        rw [← a_is_extension, other_value] at at_x
        exact absurd at_x (by decide)
      simp [not_extension]
  · obtain ⟨chosen, chosen_fixed⟩ := blocks x on_x
    have chosen_is_tuple : chosen = tuple ⟨x, on_x⟩ := by
      have at_chosen := chosen_fixed.1 chosen
      have self_true : decide (chosen = chosen) = true := by simp
      rw [other_encodes ⟨x, on_x⟩ chosen, self_true] at at_chosen
      exact of_decide_eq_true at_chosen
    have candidate_at_x : candidate x = tuple ⟨x, on_x⟩ := congrFun restricted ⟨x, on_x⟩
    show other (Sum.inr ⟨⟨x, on_x⟩, i⟩) = decide (i.val < (candidate x).val)
    rw [chosen_fixed.2 i, chosen_is_tuple, candidate_at_x]

theorem partial_support_parsimonious_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) :
    is_parsimonious csp originals (partial_support_encoding csp originals) ↔
      has_unique_extension csp originals := by
  rw [is_parsimonious_iff_unique_models csp originals originals _
    (partial_support_is_projection_exact csp originals tree has_original)]
  unfold has_unique_extension
  refine forall_congr' fun tuple => forall_congr' fun tuple_relation => ?_
  rw [extension_count_eq_one_iff]
  constructor
  · intro unique_model
    obtain ⟨candidate, solution, restricted⟩ := tuple_relation
    refine ⟨candidate, ⟨solution, restricted⟩, ?_⟩
    rintro other ⟨other_solution, other_restricted⟩
    have encodes_of : ∀ extension : assignment csp,
        restrict_to_originals csp originals extension = tuple →
        encodes_tuple csp originals originals
          (valuation_of_assignment csp originals extension) tuple := by
      intro extension extension_restricted
      rw [← extension_restricted]
      exact valuation_of_assignment_encodes csp originals originals extension
    exact valuation_of_assignment_injective csp originals (unique_model.unique
      ⟨valuation_of_solution_is_partial_support_model csp originals other other_solution,
        encodes_of other other_restricted⟩
      ⟨valuation_of_solution_is_partial_support_model csp originals candidate solution,
        encodes_of candidate restricted⟩)
  · intro unique_extension
    exact partial_support_unique_model_of_unique_extension csp originals tree has_original tuple
      unique_extension

def is_union_of_extensions (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) (valuation : boolean_variable csp originals → Bool)
    (extensions : Set (assignment csp)) : Prop :=
  extensions.Nonempty ∧
    (∀ candidate ∈ extensions, is_solution csp candidate ∧
      restrict_to_originals csp originals candidate = tuple) ∧
    (∀ x (a : Fin (csp.domain_size x)),
      valuation (Sum.inl ⟨x, a⟩) = true ↔ ∃ candidate ∈ extensions, candidate x = a) ∧
    ∀ (x : original_vertex originals) (i : Fin (csp.domain_size x.val - 1)),
      valuation (Sum.inr ⟨x, i⟩) = decide (i.val < (tuple x).val)

theorem union_of_extensions_determines_valuation (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals)
    (first second : boolean_variable csp originals → Bool) (extensions : Set (assignment csp))
    (first_union : is_union_of_extensions csp originals tuple first extensions)
    (second_union : is_union_of_extensions csp originals tuple second extensions) :
    first = second := by
  funext variable_name
  rcases variable_name with ⟨x, a⟩ | ⟨x, i⟩
  · have first_iff := first_union.2.2.1 x a
    have second_iff := second_union.2.2.1 x a
    exact Bool.eq_iff_iff.mpr (first_iff.trans second_iff.symm)
  · rw [first_union.2.2.2 x i, second_union.2.2.2 x i]

theorem partial_support_models_are_unions (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) (tuple : original_tuple csp originals)
    (valuation : boolean_variable csp originals → Bool) :
    (is_model valuation (partial_support_encoding csp originals) ∧
        encodes_tuple csp originals originals valuation tuple) ↔
      ∃ extensions, is_union_of_extensions csp originals tuple valuation extensions := by
  constructor
  · rintro ⟨model, encodes⟩
    obtain ⟨blocks, _⟩ := (is_model_partial_support_iff csp originals valuation).mp model
    refine ⟨{candidate | is_solution csp candidate ∧
      restrict_to_originals csp originals candidate = tuple ∧
      ∀ y, valuation (Sum.inl ⟨y, candidate y⟩) = true}, ?_, ?_, ?_, ?_⟩
    · obtain ⟨candidate, solution, restricted, all_selected⟩ :=
        partial_support_model_has_selected_extension csp originals tree has_original valuation model
          tuple encodes
      exact ⟨candidate, solution, restricted, all_selected⟩
    · rintro candidate ⟨solution, restricted, _⟩
      exact ⟨solution, restricted⟩
    · intro x a
      constructor
      · intro a_selected
        obtain ⟨candidate, solution, candidate_x, all_selected⟩ := partial_support_model_extends csp
          originals tree valuation model x a a_selected
        exact ⟨candidate, ⟨solution, selected_candidate_restricts csp originals originals valuation
          tuple encodes candidate all_selected, all_selected⟩, candidate_x⟩
      · rintro ⟨candidate, ⟨_, _, all_selected⟩, candidate_x⟩
        rw [← candidate_x]
        exact all_selected x
    · rintro ⟨x, on_x⟩ i
      obtain ⟨chosen, chosen_fixed⟩ := blocks x on_x
      have chosen_is_tuple : chosen = tuple ⟨x, on_x⟩ := by
        have at_chosen := chosen_fixed.1 chosen
        have self_true : decide (chosen = chosen) = true := by simp
        rw [encodes ⟨x, on_x⟩ chosen, self_true] at at_chosen
        exact of_decide_eq_true at_chosen
      rw [chosen_fixed.2 i, chosen_is_tuple]
  · rintro ⟨extensions, ⟨first_extension, first_member⟩, all_extensions, selects, ladders⟩
    have original_iff : ∀ x : original_vertex originals, ∀ a : Fin (csp.domain_size x.val),
        valuation (Sum.inl ⟨x.val, a⟩) = decide (a = tuple x) := by
      intro x a
      by_cases a_is_tuple : a = tuple x
      · have first_at_x : first_extension x.val = tuple x :=
          congrFun (all_extensions first_extension first_member).2 x
        have selected : valuation (Sum.inl ⟨x.val, a⟩) = true :=
          (selects x.val a).mpr ⟨first_extension, first_member, first_at_x.trans a_is_tuple.symm⟩
        rw [selected]
        simp [a_is_tuple]
      · have not_selected : valuation (Sum.inl ⟨x.val, a⟩) ≠ true := by
          intro selected
          obtain ⟨candidate, member, candidate_x⟩ := (selects x.val a).mp selected
          have candidate_at_x : candidate x.val = tuple x :=
            congrFun (all_extensions candidate member).2 x
          exact a_is_tuple (candidate_x.symm.trans candidate_at_x)
        have is_false : valuation (Sum.inl ⟨x.val, a⟩) = false := by simpa using not_selected
        rw [is_false]
        simp [a_is_tuple]
    refine ⟨(is_model_partial_support_iff csp originals valuation).mpr ⟨?_, ?_⟩, original_iff⟩
    · intro x on_x
      exact ⟨tuple ⟨x, on_x⟩, fun a => original_iff ⟨x, on_x⟩ a, fun i => ladders ⟨x, on_x⟩ i⟩
    · intro x y adjacent_x_y a a_selected
      obtain ⟨candidate, member, candidate_x⟩ := (selects x a).mp a_selected
      refine ⟨candidate y, ?_, (selects y _).mpr ⟨candidate, member, rfl⟩⟩
      rw [← candidate_x]
      exact (all_extensions candidate member).1 x y adjacent_x_y

open Classical in
noncomputable def valuation_of_all_extensions (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals) :
    boolean_variable csp originals → Bool
  | Sum.inl pair => decide (∃ candidate, is_solution csp candidate ∧
      restrict_to_originals csp originals candidate = tuple ∧ candidate pair.1 = pair.2)
  | Sum.inr pair => decide (pair.2.val < (tuple pair.1).val)

theorem valuation_of_all_extensions_is_union (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals)
    (tuple_relation : in_relation csp originals tuple) :
    is_union_of_extensions csp originals tuple (valuation_of_all_extensions csp originals tuple)
      {candidate | is_solution csp candidate ∧
        restrict_to_originals csp originals candidate = tuple} := by
  classical
  obtain ⟨first_extension, first_solution, first_restricted⟩ := tuple_relation
  refine ⟨⟨first_extension, first_solution, first_restricted⟩, fun _ member => member, ?_, ?_⟩
  · intro x a
    simp only [valuation_of_all_extensions, decide_eq_true_eq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨candidate, solution, restricted, candidate_x⟩
      exact ⟨candidate, ⟨solution, restricted⟩, candidate_x⟩
    · rintro ⟨candidate, ⟨solution, restricted⟩, candidate_x⟩
      exact ⟨candidate, solution, restricted, candidate_x⟩
  · intro x i
    rfl

theorem singleton_valuation_is_only_for_one_extension (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals)
    (fixed_extension : assignment csp)
    (same_valuation : valuation_of_assignment csp originals fixed_extension =
      valuation_of_all_extensions csp originals tuple)
    (candidate : assignment csp) (solution : is_solution csp candidate)
    (restricted : restrict_to_originals csp originals candidate = tuple) :
    candidate = fixed_extension := by
  classical
  funext x
  have at_candidate := congrFun same_valuation (Sum.inl ⟨x, candidate x⟩)
  have right_true : valuation_of_all_extensions csp originals tuple
      (Sum.inl ⟨x, candidate x⟩) = true := by
    simp only [valuation_of_all_extensions, decide_eq_true_eq]
    exact ⟨candidate, solution, restricted, rfl⟩
  rw [right_true] at at_candidate
  exact of_decide_eq_true at_candidate

theorem more_partial_support_models_than_extensions (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) (tuple : original_tuple csp originals)
    (several_extensions : 1 < extension_count csp originals tuple) :
    extension_count csp originals tuple <
      models_over_tuple csp originals originals (partial_support_encoding csp originals) tuple := by
  classical
  have tuple_relation : in_relation csp originals tuple := by
    unfold extension_count at several_extensions
    have positive : 0 < Fintype.card {candidate : assignment csp //
        is_solution csp candidate ∧ restrict_to_originals csp originals candidate = tuple} := by
      omega
    obtain ⟨extension⟩ := Fintype.card_pos_iff.mp positive
    exact ⟨extension.val, extension.property.1, extension.property.2⟩
  obtain ⟨all_model, all_encodes⟩ := (partial_support_models_are_unions csp originals tree
    has_original tuple (valuation_of_all_extensions csp originals tuple)).mpr
    ⟨_, valuation_of_all_extensions_is_union csp originals tuple tuple_relation⟩
  unfold extension_count models_over_tuple at *
  let to_model : {candidate : assignment csp // is_solution csp candidate ∧
      restrict_to_originals csp originals candidate = tuple} →
      {valuation : boolean_variable csp originals → Bool //
        is_model valuation (partial_support_encoding csp originals) ∧
          encodes_tuple csp originals originals valuation tuple} :=
    fun candidate =>
      ⟨valuation_of_assignment csp originals candidate.val,
        valuation_of_solution_is_partial_support_model csp originals candidate.val
          candidate.property.1, by
          have encodes := valuation_of_assignment_encodes csp originals originals candidate.val
          rw [candidate.property.2] at encodes
          exact encodes⟩
  have to_model_injective : Function.Injective to_model := by
    intro first second same_image
    exact Subtype.ext (valuation_of_assignment_injective csp originals
      (congrArg Subtype.val same_image))
  refine Fintype.card_lt_of_injective_of_notMem to_model to_model_injective
    (b := ⟨valuation_of_all_extensions csp originals tuple, all_model, all_encodes⟩) ?_
  rintro ⟨fixed_extension, same_image⟩
  have same_valuation := congrArg Subtype.val same_image
  have all_equal : ∀ first second : {candidate : assignment csp //
      is_solution csp candidate ∧ restrict_to_originals csp originals candidate = tuple},
      first = second := by
    intro first second
    apply Subtype.ext
    rw [singleton_valuation_is_only_for_one_extension csp originals tuple fixed_extension.val
        same_valuation first.val first.property.1 first.property.2,
      singleton_valuation_is_only_for_one_extension csp originals tuple fixed_extension.val
        same_valuation second.val second.property.1 second.property.2]
  have at_most_one := Fintype.card_le_one_iff.mpr all_equal
  omega

theorem partial_support_same_count_as_support_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) :
    model_count (partial_support_encoding csp originals) = model_count (support_encoding csp) ↔
      has_unique_extension csp originals := by
  classical
  constructor
  · intro same_count tuple tuple_relation
    rw [extension_count_eq_one_iff]
    rw [support_model_count] at same_count
    unfold model_count at same_count
    let to_model : {candidate : assignment csp // is_solution csp candidate} →
        {valuation : boolean_variable csp originals → Bool //
          is_model valuation (partial_support_encoding csp originals)} :=
      fun candidate =>
        ⟨valuation_of_assignment csp originals candidate.val,
          valuation_of_solution_is_partial_support_model csp originals candidate.val
            candidate.property⟩
    have to_model_injective : Function.Injective to_model := by
      intro first second same_image
      exact Subtype.ext (valuation_of_assignment_injective csp originals
        (congrArg Subtype.val same_image))
    have to_model_bijective : Function.Bijective to_model :=
      (Fintype.bijective_iff_injective_and_card to_model).mpr
        ⟨to_model_injective, same_count.symm⟩
    obtain ⟨all_model, _⟩ := (partial_support_models_are_unions csp originals tree has_original tuple
      (valuation_of_all_extensions csp originals tuple)).mpr
      ⟨_, valuation_of_all_extensions_is_union csp originals tuple tuple_relation⟩
    obtain ⟨fixed_extension, same_image⟩ := to_model_bijective.2 ⟨_, all_model⟩
    have same_valuation := congrArg Subtype.val same_image
    obtain ⟨candidate, solution, restricted⟩ := tuple_relation
    refine ⟨candidate, ⟨solution, restricted⟩, ?_⟩
    rintro other ⟨other_solution, other_restricted⟩
    rw [singleton_valuation_is_only_for_one_extension csp originals tuple fixed_extension.val
        same_valuation other other_solution other_restricted,
      singleton_valuation_is_only_for_one_extension csp originals tuple fixed_extension.val
        same_valuation candidate solution restricted]
  · intro unique_extension
    have partial_count := (partial_support_parsimonious_iff csp originals tree has_original).mpr
      unique_extension
    have support_count := (support_parsimonious_iff csp originals).mpr unique_extension
    exact partial_count.trans support_count.symm

end parsimony
