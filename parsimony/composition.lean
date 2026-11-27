import parsimony.log_encoding

namespace parsimony

variable {original_count part_count : ℕ}

theorem is_model_rename_formula_iff {source_type target_type : Type}
    (rename : source_type → target_type) (valuation : target_type → Bool)
    (formula : cnf_formula source_type) :
    is_model valuation (rename_formula rename formula) ↔ is_model (valuation ∘ rename) formula := by
  unfold rename_formula
  constructor
  · intro model clause clause_mem
    obtain ⟨literal, literal_mem, literal_holds⟩ := model _ (List.mem_map_of_mem clause_mem)
    obtain ⟨original_literal, original_mem, rfl⟩ := List.mem_map.mp literal_mem
    exact ⟨original_literal, original_mem, literal_holds⟩
  · intro model renamed_clause renamed_mem
    obtain ⟨clause, clause_mem, rfl⟩ := List.mem_map.mp renamed_mem
    obtain ⟨literal, literal_mem, literal_holds⟩ := model clause clause_mem
    exact ⟨(rename literal.1, literal.2), List.mem_map_of_mem literal_mem, literal_holds⟩

theorem is_model_conjunction_iff (problem : composition_problem original_count part_count)
    (valuation : global_variable problem → Bool) :
    is_model valuation (conjunction_formula problem) ↔
      ∀ part, is_model (valuation ∘ rename_to_global problem part) (problem.part_formula part) := by
  unfold conjunction_formula
  rw [is_model_flatMap_iff]
  constructor
  · intro models part
    exact (is_model_rename_formula_iff _ _ _).mp (models part (List.mem_finRange part))
  · intro models part _
    exact (is_model_rename_formula_iff _ _ _).mpr (models part)

def part_valuation_of (problem : composition_problem original_count part_count)
    (part : Fin part_count) (tuple : global_tuple problem)
    (private_valuation : problem.private_type part → Bool) : part_variable problem part → Bool
  | Sum.inl ⟨member, block_variable⟩ =>
    problem.block_code (problem.scope_original part member)
      (tuple (problem.scope_original part member)) block_variable
  | Sum.inr private_variable => private_valuation private_variable

def global_valuation_of (problem : composition_problem original_count part_count)
    (tuple : global_tuple problem)
    (private_valuations : ∀ part, problem.private_type part → Bool) :
    global_variable problem → Bool
  | Sum.inl ⟨original, block_variable⟩ => problem.block_code original (tuple original) block_variable
  | Sum.inr ⟨part, private_variable⟩ => private_valuations part private_variable

theorem global_valuation_of_rename (problem : composition_problem original_count part_count)
    (tuple : global_tuple problem)
    (private_valuations : ∀ part, problem.private_type part → Bool) (part : Fin part_count) :
    global_valuation_of problem tuple private_valuations ∘ rename_to_global problem part =
      part_valuation_of problem part tuple (private_valuations part) := by
  funext variable_name
  rcases variable_name with ⟨member, block_variable⟩ | private_variable <;> rfl

theorem model_has_global_tuple (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part)
    (valuation : global_variable problem → Bool)
    (model : is_model valuation (conjunction_formula problem)) :
    ∃ tuple, satisfies_all_parts problem tuple ∧ global_encodes problem valuation tuple := by
  have models := (is_model_conjunction_iff problem valuation).mp model
  have block_value : ∀ original, ∃ value : Fin (problem.domain_size original),
      ∀ block_variable, valuation (Sum.inl ⟨original, block_variable⟩) =
        problem.block_code original value block_variable := by
    intro original
    obtain ⟨part, member, rfl⟩ := covers original
    obtain ⟨tuple, _, encodes⟩ := (exact part).1 _ (models part)
    exact ⟨tuple member, fun block_variable => encodes member block_variable⟩
  choose tuple tuple_encodes using block_value
  refine ⟨tuple, ?_, tuple_encodes⟩
  intro part
  obtain ⟨part_value, in_part_relation, encodes⟩ := (exact part).1 _ (models part)
  have same_tuple : part_value = restrict_to_part problem tuple part := by
    funext member
    apply problem.block_code_injective
    funext block_variable
    exact (encodes member block_variable).symm.trans (tuple_encodes _ block_variable)
  rw [← same_tuple]
  exact in_part_relation

theorem private_count_eq_part_models_over (problem : composition_problem original_count part_count)
    (part : Fin part_count) (tuple : global_tuple problem) :
    Fintype.card {private_valuation : problem.private_type part → Bool //
      is_model (part_valuation_of problem part tuple private_valuation) (problem.part_formula part)} =
    part_models_over problem part (restrict_to_part problem tuple part) := by
  unfold part_models_over
  refine Fintype.card_of_bijective
    (f := fun private_valuation => ⟨part_valuation_of problem part tuple private_valuation.val,
      private_valuation.property, fun _ _ => rfl⟩) ⟨?_, ?_⟩
  · intro first second same
    apply Subtype.ext
    funext private_variable
    exact congrFun (congrArg Subtype.val same) (Sum.inr private_variable)
  · rintro ⟨valuation, model, encodes⟩
    have valuation_eq : valuation = part_valuation_of problem part tuple
        (fun private_variable => valuation (Sum.inr private_variable)) := by
      funext variable_name
      rcases variable_name with ⟨member, block_variable⟩ | private_variable
      · exact encodes member block_variable
      · rfl
    refine ⟨⟨fun private_variable => valuation (Sum.inr private_variable), ?_⟩, ?_⟩
    · rw [← valuation_eq]
      exact model
    · exact Subtype.ext valuation_eq.symm

theorem composition_model_count (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part) :
    model_count (conjunction_formula problem) =
      ∑ tuple ∈ Finset.univ.filter (satisfies_all_parts problem),
        ∏ part, part_models_over problem part (restrict_to_part problem tuple part) := by
  have model_bijection : model_count (conjunction_formula problem) =
      Fintype.card {choice : global_tuple problem × (∀ part, problem.private_type part → Bool) //
        satisfies_all_parts problem choice.1 ∧
          ∀ part, is_model (part_valuation_of problem part choice.1 (choice.2 part))
            (problem.part_formula part)} := by
    unfold model_count
    symm
    refine Fintype.card_of_bijective
      (f := fun choice => ⟨global_valuation_of problem choice.val.1 choice.val.2, by
        rw [is_model_conjunction_iff]
        intro part
        rw [global_valuation_of_rename]
        exact choice.property.2 part⟩) ⟨?_, ?_⟩
    · rintro ⟨⟨first_tuple, first_private⟩, first_property⟩
        ⟨⟨second_tuple, second_private⟩, second_property⟩ same
      have same_valuation := congrArg Subtype.val same
      have tuples_equal : first_tuple = second_tuple := by
        funext original
        apply problem.block_code_injective original
        funext block_variable
        exact congrFun same_valuation (Sum.inl ⟨original, block_variable⟩)
      have privates_equal : first_private = second_private := by
        funext part private_variable
        exact congrFun same_valuation (Sum.inr ⟨part, private_variable⟩)
      subst tuples_equal
      subst privates_equal
      rfl
    · rintro ⟨valuation, model⟩
      obtain ⟨tuple, satisfied, encodes⟩ :=
        model_has_global_tuple problem covers exact valuation model
      have valuation_eq : valuation = global_valuation_of problem tuple
          (fun part private_variable => valuation (Sum.inr ⟨part, private_variable⟩)) := by
        funext variable_name
        rcases variable_name with ⟨original, block_variable⟩ | ⟨part, private_variable⟩
        · exact encodes original block_variable
        · rfl
      refine ⟨⟨(tuple, fun part private_variable => valuation (Sum.inr ⟨part, private_variable⟩)),
        satisfied, ?_⟩, ?_⟩
      · intro part
        have part_model := (is_model_conjunction_iff problem valuation).mp model part
        rw [valuation_eq, global_valuation_of_rename] at part_model
        exact part_model
      · exact Subtype.ext valuation_eq.symm
  rw [model_bijection, Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      fun (tuple : global_tuple problem)
        (private_valuations : ∀ part, problem.private_type part → Bool) =>
        satisfies_all_parts problem tuple ∧
          ∀ part, is_model (part_valuation_of problem part tuple (private_valuations part))
            (problem.part_formula part)),
    Fintype.card_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun tuple _ => ?_
  split_ifs with satisfied
  · have pi_equiv : {private_valuations : ∀ part, problem.private_type part → Bool //
          satisfies_all_parts problem tuple ∧
            ∀ part, is_model (part_valuation_of problem part tuple (private_valuations part))
              (problem.part_formula part)} ≃
        ∀ part, {private_valuation : problem.private_type part → Bool //
          is_model (part_valuation_of problem part tuple private_valuation)
            (problem.part_formula part)} :=
      (Equiv.subtypeEquivRight fun _ => and_iff_right satisfied).trans
        (Equiv.subtypePiEquivPi (p := fun part private_valuation =>
          is_model (part_valuation_of problem part tuple private_valuation)
            (problem.part_formula part)))
    rw [Fintype.card_congr pi_equiv, Fintype.card_pi]
    exact Finset.prod_congr rfl fun part _ => private_count_eq_part_models_over problem part tuple
  · rw [Fintype.card_eq_zero_iff]
    exact ⟨fun choice => satisfied choice.property.1⟩

theorem composition_factor_positive (problem : composition_problem original_count part_count)
    (exact : ∀ part, part_is_projection_exact problem part) (tuple : global_tuple problem)
    (satisfied : satisfies_all_parts problem tuple) (part : Fin part_count) :
    0 < part_models_over problem part (restrict_to_part problem tuple part) := by
  obtain ⟨valuation, model, encodes⟩ := (exact part).2 _ (satisfied part)
  unfold part_models_over
  exact Fintype.card_pos_iff.mpr ⟨⟨valuation, model, encodes⟩⟩

theorem composition_projection_exact (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part) :
    (∀ valuation, is_model valuation (conjunction_formula problem) →
      ∃ tuple, satisfies_all_parts problem tuple ∧ global_encodes problem valuation tuple) ∧
    (∀ tuple, satisfies_all_parts problem tuple →
      ∃ valuation, is_model valuation (conjunction_formula problem) ∧
        global_encodes problem valuation tuple) := by
  refine ⟨model_has_global_tuple problem covers exact, ?_⟩
  intro tuple satisfied
  have part_models : ∀ part, ∃ valuation : part_variable problem part → Bool,
      is_model valuation (problem.part_formula part) ∧
        part_encodes problem part valuation (restrict_to_part problem tuple part) :=
    fun part => (exact part).2 _ (satisfied part)
  choose part_valuation part_model part_encodes_tuple using part_models
  refine ⟨global_valuation_of problem tuple
    (fun part private_variable => part_valuation part (Sum.inr private_variable)), ?_, fun _ _ => rfl⟩
  rw [is_model_conjunction_iff]
  intro part
  rw [global_valuation_of_rename]
  have valuation_eq : part_valuation part = part_valuation_of problem part tuple
      (fun private_variable => part_valuation part (Sum.inr private_variable)) := by
    funext variable_name
    rcases variable_name with ⟨member, block_variable⟩ | private_variable
    · exact part_encodes_tuple part member block_variable
    · rfl
  rw [← valuation_eq]
  exact part_model part

theorem composition_parsimonious_iff (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part) :
    model_count (conjunction_formula problem) =
        (Finset.univ.filter (satisfies_all_parts problem)).card ↔
      ∀ tuple, satisfies_all_parts problem tuple →
        ∀ part, part_models_over problem part (restrict_to_part problem tuple part) = 1 := by
  rw [composition_model_count problem covers exact, Finset.card_eq_sum_ones]
  constructor
  · intro sums_equal tuple satisfied part
    have each_ge : ∀ other ∈ Finset.univ.filter (satisfies_all_parts problem),
        1 ≤ ∏ part, part_models_over problem part (restrict_to_part problem other part) := by
      intro other other_mem
      have other_satisfied := (Finset.mem_filter.mp other_mem).2
      exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun part _ =>
        composition_factor_positive problem exact other other_satisfied part).ne'
    have products_one := (Finset.sum_eq_sum_iff_of_le each_ge).mp sums_equal.symm tuple
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, satisfied⟩)
    exact Nat.dvd_one.mp (products_one ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ part))
  · intro all_one
    refine Finset.sum_congr rfl fun tuple tuple_mem => ?_
    have satisfied := (Finset.mem_filter.mp tuple_mem).2
    exact Finset.prod_eq_one fun part _ => all_one tuple satisfied part

theorem composition_parsimonious_of_parsimonious_parts
    (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part)
    (parts_parsimonious : ∀ part tuple, problem.part_relation part tuple →
      part_models_over problem part tuple = 1) :
    model_count (conjunction_formula problem) =
      (Finset.univ.filter (satisfies_all_parts problem)).card :=
  (composition_parsimonious_iff problem covers exact).mpr
    fun _ satisfied part => parts_parsimonious part _ (satisfied part)

end parsimony
