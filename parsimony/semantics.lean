import parsimony.ladder
import parsimony.tree_order

namespace parsimony

variable {vertex_count : ℕ}

theorem is_model_append {boolean_type : Type} (valuation : boolean_type → Bool)
    (first second : cnf_formula boolean_type) :
    is_model valuation (first ++ second) ↔ is_model valuation first ∧ is_model valuation second := by
  simp only [is_model, List.mem_append]
  constructor
  · intro all_hold
    exact ⟨fun clause member => all_hold clause (Or.inl member),
      fun clause member => all_hold clause (Or.inr member)⟩
  · rintro ⟨first_holds, second_holds⟩ clause (member | member)
    · exact first_holds clause member
    · exact second_holds clause member

def block_is_fixed (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (x : Fin vertex_count)
    (on_x : ladder_on x = true) (chosen : Fin (csp.domain_size x)) : Prop :=
  (∀ a : Fin (csp.domain_size x), valuation (Sum.inl ⟨x, a⟩) = decide (a = chosen)) ∧
    ∀ i : Fin (csp.domain_size x - 1),
      valuation (Sum.inr ⟨⟨x, on_x⟩, i⟩) = decide (i.val < chosen.val)

theorem is_model_exactly_one_part_iff (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (valuation : boolean_variable csp ladder_on → Bool) :
    is_model valuation (exactly_one_part csp ladder_on) ↔
      ∀ x (on_x : ladder_on x = true), ∃ chosen, block_is_fixed csp ladder_on valuation x on_x chosen := by
  have block_iff : ∀ x (on_x : ladder_on x = true),
      (∀ clause ∈ exactly_one_clauses (csp.domain_size x) (value_literal csp ladder_on x)
          (ladder_literal csp ladder_on ⟨x, on_x⟩),
          ∃ literal ∈ clause, valuation literal.1 = literal.2) ↔
        ∃ chosen, block_is_fixed csp ladder_on valuation x on_x chosen := by
    intro x on_x
    exact exactly_one_clauses_hold_iff (csp.domain_nonempty x) (value_literal csp ladder_on x)
      (ladder_literal csp ladder_on ⟨x, on_x⟩)
      (fun literal => valuation literal.1 = literal.2)
      (fun a => valuation (Sum.inl ⟨x, a⟩))
      (fun i => valuation (Sum.inr ⟨⟨x, on_x⟩, i⟩))
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
  constructor
  · intro model x on_x
    refine (block_iff x on_x).mp ?_
    intro clause clause_member
    refine model clause (List.mem_flatMap.mpr ⟨x, List.mem_finRange x, ?_⟩)
    simpa [on_x] using clause_member
  · intro blocks clause clause_member
    obtain ⟨x, _, member_of_x⟩ := List.mem_flatMap.mp clause_member
    by_cases on_x : ladder_on x = true
    · have member : clause ∈ exactly_one_clauses (csp.domain_size x) (value_literal csp ladder_on x)
          (ladder_literal csp ladder_on ⟨x, on_x⟩) := by
        simpa [on_x] using member_of_x
      exact (block_iff x on_x).mpr (blocks x on_x) clause member
    · simp [on_x] at member_of_x

theorem is_model_clauses_on_chosen_pairs_iff {boolean_type : Type} (valuation : boolean_type → Bool)
    (chosen : Fin vertex_count → Fin vertex_count → Bool)
    (clauses_of_pair : Fin vertex_count → Fin vertex_count → cnf_formula boolean_type) :
    is_model valuation (clauses_on_chosen_pairs chosen clauses_of_pair) ↔
      ∀ x y, chosen x y = true → is_model valuation (clauses_of_pair x y) := by
  constructor
  · intro model x y chosen_x_y clause clause_member
    refine model clause (List.mem_flatMap.mpr ⟨x, List.mem_finRange x,
      List.mem_flatMap.mpr ⟨y, List.mem_finRange y, ?_⟩⟩)
    simpa [chosen_x_y] using clause_member
  · intro pairs_hold clause clause_member
    obtain ⟨x, _, member_of_x⟩ := List.mem_flatMap.mp clause_member
    obtain ⟨y, _, member_of_y⟩ := List.mem_flatMap.mp member_of_x
    by_cases chosen_x_y : chosen x y = true
    · have member : clause ∈ clauses_of_pair x y := by
        simpa [chosen_x_y] using member_of_y
      exact pairs_hold x y chosen_x_y clause member
    · simp [chosen_x_y] at member_of_y

def edge_is_supported (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (x y : Fin vertex_count) : Prop :=
  ∀ a : Fin (csp.domain_size x), valuation (Sum.inl ⟨x, a⟩) = true →
    ∃ b : Fin (csp.domain_size y),
      csp.allowed x y a b = true ∧ valuation (Sum.inl ⟨y, b⟩) = true

theorem clause_holds_support_clause_iff (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (valuation : boolean_variable csp ladder_on → Bool)
    (x y : Fin vertex_count) (a : Fin (csp.domain_size x)) :
    clause_holds valuation (support_clause csp ladder_on x y a) ↔
      (valuation (Sum.inl ⟨x, a⟩) = true →
        ∃ b : Fin (csp.domain_size y),
          csp.allowed x y a b = true ∧ valuation (Sum.inl ⟨y, b⟩) = true) := by
  simp only [clause_holds, support_clause, value_literal, List.mem_cons, exists_eq_or_imp,
    List.mem_map, List.mem_filter, List.mem_finRange, true_and, exists_exists_and_eq_and]
  constructor
  · rintro (is_false | supported) is_true
    · rw [is_true] at is_false
      exact absurd is_false (by decide)
    · exact supported
  · intro implication
    cases value_case : valuation (Sum.inl ⟨x, a⟩) with
    | false => exact Or.inl rfl
    | true => exact Or.inr (implication value_case)

theorem is_model_support_clauses_of_pair_iff (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (valuation : boolean_variable csp ladder_on → Bool)
    (x y : Fin vertex_count) :
    is_model valuation (support_clauses_of_pair csp ladder_on x y) ↔
      edge_is_supported csp ladder_on valuation x y := by
  simp only [is_model, support_clauses_of_pair, List.mem_map, List.mem_finRange, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, clause_holds_support_clause_iff]
  rfl

def edge_respects_relation (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (x y : Fin vertex_count) : Prop :=
  ∀ (a : Fin (csp.domain_size x)) (b : Fin (csp.domain_size y)),
    csp.allowed x y a b = false →
      valuation (Sum.inl ⟨x, a⟩) = false ∨ valuation (Sum.inl ⟨y, b⟩) = false

theorem is_model_forbidden_clauses_of_pair_iff (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (valuation : boolean_variable csp ladder_on → Bool)
    (x y : Fin vertex_count) :
    is_model valuation (forbidden_clauses_of_pair csp ladder_on x y) ↔
      edge_respects_relation csp ladder_on valuation x y := by
  constructor
  · intro model a b forbidden
    have holds := model [value_literal csp ladder_on x a false, value_literal csp ladder_on y b false]
      (List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_map.mpr
        ⟨b, List.mem_filter.mpr ⟨List.mem_finRange b, by simp [forbidden]⟩, rfl⟩⟩)
    simpa [clause_holds, value_literal] using holds
  · intro respects clause clause_member
    obtain ⟨a, _, member_of_a⟩ := List.mem_flatMap.mp clause_member
    obtain ⟨b, b_filter, clause_is⟩ := List.mem_map.mp member_of_a
    subst clause_is
    have forbidden : csp.allowed x y a b = false := by
      simpa using (List.mem_filter.mp b_filter).2
    simpa [clause_holds, value_literal] using respects a b forbidden

theorem is_model_minimal_support_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (valuation : boolean_variable csp originals → Bool) :
    is_model valuation (minimal_support_encoding csp originals order) ↔
      (∀ x (on_x : originals x = true),
        ∃ chosen, block_is_fixed csp originals valuation x on_x chosen) ∧
      ∀ x y, csp.adjacent x y = true → earlier_in order x y = true →
        edge_is_supported csp originals valuation x y := by
  rw [minimal_support_encoding, is_model_append, is_model_exactly_one_part_iff,
    tree_order_support_clauses, is_model_clauses_on_chosen_pairs_iff]
  simp only [Bool.and_eq_true, is_model_support_clauses_of_pair_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    exact ⟨blocks, fun x y adjacent_x_y x_earlier => edges x y ⟨adjacent_x_y, x_earlier⟩⟩
  · rintro ⟨blocks, edges⟩
    exact ⟨blocks, fun x y chosen => edges x y chosen.1 chosen.2⟩

theorem is_model_partial_support_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (valuation : boolean_variable csp originals → Bool) :
    is_model valuation (partial_support_encoding csp originals) ↔
      (∀ x (on_x : originals x = true),
        ∃ chosen, block_is_fixed csp originals valuation x on_x chosen) ∧
      ∀ x y, csp.adjacent x y = true → edge_is_supported csp originals valuation x y := by
  rw [partial_support_encoding, is_model_append, is_model_exactly_one_part_iff,
    all_support_clauses, is_model_clauses_on_chosen_pairs_iff]
  simp only [is_model_support_clauses_of_pair_iff]

theorem is_model_support_iff (csp : binary_csp vertex_count)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (support_encoding csp) ↔
      (∀ x (on_x : all_vertices x = true),
        ∃ chosen, block_is_fixed csp all_vertices valuation x on_x chosen) ∧
      ∀ x y, csp.adjacent x y = true → edge_is_supported csp all_vertices valuation x y := by
  rw [support_encoding, is_model_append, is_model_exactly_one_part_iff,
    all_support_clauses, is_model_clauses_on_chosen_pairs_iff]
  simp only [is_model_support_clauses_of_pair_iff]

theorem is_model_min_eo_iff (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (min_eo_encoding csp order) ↔
      (∀ x (on_x : all_vertices x = true),
        ∃ chosen, block_is_fixed csp all_vertices valuation x on_x chosen) ∧
      ∀ x y, csp.adjacent x y = true → earlier_in order x y = true →
        edge_is_supported csp all_vertices valuation x y := by
  rw [min_eo_encoding, is_model_append, is_model_exactly_one_part_iff,
    tree_order_support_clauses, is_model_clauses_on_chosen_pairs_iff]
  simp only [Bool.and_eq_true, is_model_support_clauses_of_pair_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    exact ⟨blocks, fun x y adjacent_x_y x_earlier => edges x y ⟨adjacent_x_y, x_earlier⟩⟩
  · rintro ⟨blocks, edges⟩
    exact ⟨blocks, fun x y chosen => edges x y chosen.1 chosen.2⟩

theorem is_model_direct_iff (csp : binary_csp vertex_count)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (direct_encoding csp) ↔
      (∀ x (on_x : all_vertices x = true),
        ∃ chosen, block_is_fixed csp all_vertices valuation x on_x chosen) ∧
      ∀ x y, csp.adjacent x y = true → edge_respects_relation csp all_vertices valuation x y := by
  rw [direct_encoding, is_model_append, is_model_exactly_one_part_iff,
    all_forbidden_clauses, is_model_clauses_on_chosen_pairs_iff]
  simp only [is_model_forbidden_clauses_of_pair_iff]

def valuation_of_assignment (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (candidate : assignment csp) : boolean_variable csp ladder_on → Bool
  | Sum.inl pair => decide (pair.2 = candidate pair.1)
  | Sum.inr pair => decide (pair.2.val < (candidate pair.1.val).val)

theorem valuation_of_assignment_block (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (candidate : assignment csp) (x : Fin vertex_count)
    (on_x : ladder_on x = true) :
    block_is_fixed csp ladder_on (valuation_of_assignment csp ladder_on candidate) x on_x
      (candidate x) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem valuation_of_solution_edge (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (candidate : assignment csp)
    (solution : is_solution csp candidate) (x y : Fin vertex_count)
    (adjacent_x_y : csp.adjacent x y = true) :
    edge_is_supported csp ladder_on (valuation_of_assignment csp ladder_on candidate) x y := by
  intro a a_selected
  have a_is_candidate : a = candidate x := by
    simpa [valuation_of_assignment] using a_selected
  refine ⟨candidate y, ?_, ?_⟩
  · rw [a_is_candidate]
    exact solution x y adjacent_x_y
  · simp [valuation_of_assignment]

theorem valuation_of_assignment_injective (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) :
    Function.Injective (valuation_of_assignment csp ladder_on) := by
  intro first second same_valuation
  funext x
  have at_first := congrFun same_valuation (Sum.inl ⟨x, first x⟩)
  simp only [valuation_of_assignment, decide_true] at at_first
  have is_equal := of_decide_eq_true at_first.symm
  exact is_equal

theorem encodes_tuple_unique (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (first second : original_tuple csp originals)
    (encodes_first : encodes_tuple csp originals ladder_on valuation first)
    (encodes_second : encodes_tuple csp originals ladder_on valuation second) : first = second := by
  funext x
  have at_first := encodes_first x (first x)
  rw [encodes_second x (first x)] at at_first
  simpa using at_first

theorem valuation_of_assignment_encodes (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool) (candidate : assignment csp) :
    encodes_tuple csp originals ladder_on (valuation_of_assignment csp ladder_on candidate)
      (restrict_to_originals csp originals candidate) :=
  fun _ _ => rfl

theorem is_parsimonious_iff_unique_models (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (formula : cnf_formula (boolean_variable csp ladder_on))
    (projection_exact : is_projection_exact csp originals ladder_on formula) :
    is_parsimonious csp originals formula ↔
      ∀ tuple, in_relation csp originals tuple →
        ∃! valuation, is_model valuation formula ∧
          encodes_tuple csp originals ladder_on valuation tuple := by
  classical
  choose tuple_of tuple_in_relation tuple_encoded using
    fun model : {valuation : boolean_variable csp ladder_on → Bool // is_model valuation formula} =>
      projection_exact.1 model.val model.property
  let to_tuple : {valuation : boolean_variable csp ladder_on → Bool // is_model valuation formula} →
      {tuple : original_tuple csp originals // in_relation csp originals tuple} :=
    fun model => ⟨tuple_of model, tuple_in_relation model⟩
  have to_tuple_surjective : Function.Surjective to_tuple := by
    rintro ⟨tuple, tuple_relation⟩
    obtain ⟨valuation, model, encodes⟩ := projection_exact.2 tuple tuple_relation
    refine ⟨⟨valuation, model⟩, Subtype.ext ?_⟩
    exact encodes_tuple_unique csp originals ladder_on valuation _ _
      (tuple_encoded ⟨valuation, model⟩) encodes
  have bijective_iff := Fintype.bijective_iff_surjective_and_card to_tuple
  constructor
  · intro parsimonious tuple tuple_relation
    have bijective : Function.Bijective to_tuple :=
      bijective_iff.mpr ⟨to_tuple_surjective, parsimonious⟩
    obtain ⟨valuation, model, encodes⟩ := projection_exact.2 tuple tuple_relation
    refine ⟨valuation, ⟨model, encodes⟩, ?_⟩
    rintro other ⟨other_model, other_encodes⟩
    have same_image : to_tuple ⟨other, other_model⟩ = to_tuple ⟨valuation, model⟩ := by
      apply Subtype.ext
      have first_same := encodes_tuple_unique csp originals ladder_on other _ tuple
        (tuple_encoded ⟨other, other_model⟩) other_encodes
      have second_same := encodes_tuple_unique csp originals ladder_on valuation _ tuple
        (tuple_encoded ⟨valuation, model⟩) encodes
      exact first_same.trans second_same.symm
    exact congrArg Subtype.val (bijective.1 same_image)
  · intro unique_models
    have injective : Function.Injective to_tuple := by
      intro first second same_image
      have same_tuple : tuple_of first = tuple_of second := congrArg Subtype.val same_image
      have first_over := tuple_encoded first
      have second_over := tuple_encoded second
      rw [← same_tuple] at second_over
      exact Subtype.ext ((unique_models (tuple_of first) (tuple_in_relation first)).unique
        ⟨first.property, first_over⟩ ⟨second.property, second_over⟩)
    exact (bijective_iff.mp ⟨injective, to_tuple_surjective⟩).2

end parsimony
