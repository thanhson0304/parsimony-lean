import parsimony.composition_link_log

namespace parsimony

variable {original_count part_count : ℕ}

section abstract_block_test

def composition_kept_variables (problem : composition_problem original_count part_count)
    (kept_private : ∀ part, Finset (problem.private_type part)) :
    Finset (global_variable problem) :=
  Finset.disjSum Finset.univ (Finset.univ.sigma kept_private)

theorem shared_mem_composition_kept (problem : composition_problem original_count part_count)
    (kept_private : ∀ part, Finset (problem.private_type part))
    (shared_variable : Σ original, problem.block_type original) :
    (Sum.inl shared_variable : global_variable problem) ∈
      composition_kept_variables problem kept_private :=
  Finset.inl_mem_disjSum.mpr (Finset.mem_univ shared_variable)

theorem private_mem_composition_kept_iff (problem : composition_problem original_count part_count)
    (kept_private : ∀ part, Finset (problem.private_type part)) (part : Fin part_count)
    (private_variable : problem.private_type part) :
    (Sum.inr ⟨part, private_variable⟩ : global_variable problem) ∈
        composition_kept_variables problem kept_private ↔
      private_variable ∈ kept_private part := by
  unfold composition_kept_variables
  rw [Finset.inr_mem_disjSum, Finset.mem_sigma]
  exact and_iff_right (Finset.mem_univ part)

theorem shared_of_mem_no_private (problem : composition_problem original_count part_count)
    (variable_name : global_variable problem)
    (kept : variable_name ∈ composition_kept_variables problem fun _ => ∅) :
    ∃ shared_variable, variable_name = Sum.inl shared_variable := by
  rcases variable_name with shared_variable | ⟨part, private_variable⟩
  · exact ⟨shared_variable, rfl⟩
  · rw [private_mem_composition_kept_iff] at kept
    exact absurd kept (Finset.notMem_empty private_variable)

def private_fixed_in_part (problem : composition_problem original_count part_count)
    (part : Fin part_count) (tuple : part_tuple problem part)
    (chosen : problem.private_type part → Prop) : Prop :=
  ∀ first second : part_variable problem part → Bool,
    is_model first (problem.part_formula part) → part_encodes problem part first tuple →
    is_model second (problem.part_formula part) → part_encodes problem part second tuple →
    ∀ private_variable, chosen private_variable →
      first (Sum.inr private_variable) = second (Sum.inr private_variable)

def private_fixed_in_conjunction (problem : composition_problem original_count part_count)
    (tuple : global_tuple problem) (part : Fin part_count)
    (chosen : problem.private_type part → Prop) : Prop :=
  ∀ first second : global_variable problem → Bool,
    is_model first (conjunction_formula problem) → global_encodes problem first tuple →
    is_model second (conjunction_formula problem) → global_encodes problem second tuple →
    ∀ private_variable, chosen private_variable →
      first (Sum.inr ⟨part, private_variable⟩) = second (Sum.inr ⟨part, private_variable⟩)

theorem conjunction_model_restricts (problem : composition_problem original_count part_count)
    (valuation : global_variable problem → Bool)
    (model : is_model valuation (conjunction_formula problem)) (tuple : global_tuple problem)
    (encodes : global_encodes problem valuation tuple) (part : Fin part_count) :
    is_model (valuation ∘ rename_to_global problem part) (problem.part_formula part) ∧
      part_encodes problem part (valuation ∘ rename_to_global problem part)
        (restrict_to_part problem tuple part) :=
  ⟨(is_model_conjunction_iff problem valuation).mp model part,
    fun member block_variable => encodes (problem.scope_original part member) block_variable⟩

theorem part_valuation_of_private_eq (problem : composition_problem original_count part_count)
    (part : Fin part_count) (tuple : global_tuple problem)
    (part_valuation : part_variable problem part → Bool)
    (encodes : part_encodes problem part part_valuation (restrict_to_part problem tuple part)) :
    part_valuation_of problem part tuple
        (fun private_variable => part_valuation (Sum.inr private_variable)) = part_valuation := by
  funext variable_name
  rcases variable_name with ⟨member, block_variable⟩ | private_variable
  · exact (encodes member block_variable).symm
  · rfl

theorem part_model_extends (problem : composition_problem original_count part_count)
    (exact : ∀ part, part_is_projection_exact problem part) (tuple : global_tuple problem)
    (satisfied : satisfies_all_parts problem tuple) (part : Fin part_count)
    (part_valuation : part_variable problem part → Bool)
    (model : is_model part_valuation (problem.part_formula part))
    (encodes : part_encodes problem part part_valuation (restrict_to_part problem tuple part)) :
    ∃ valuation, is_model valuation (conjunction_formula problem) ∧
      global_encodes problem valuation tuple ∧
      valuation ∘ rename_to_global problem part = part_valuation := by
  have other_models : ∀ other, ∃ other_valuation : part_variable problem other → Bool,
      is_model other_valuation (problem.part_formula other) ∧
        part_encodes problem other other_valuation (restrict_to_part problem tuple other) :=
    fun other => (exact other).2 _ (satisfied other)
  choose other_valuation other_model other_encodes using other_models
  have all_parts : ∀ other, is_model
      (part_valuation_of problem other tuple
        (Function.update
          (fun other private_variable => other_valuation other (Sum.inr private_variable))
          part (fun private_variable => part_valuation (Sum.inr private_variable)) other))
      (problem.part_formula other) := by
    refine (Function.forall_update_iff _ (fun other private_valuation =>
      is_model (part_valuation_of problem other tuple private_valuation)
        (problem.part_formula other))).mpr ⟨?_, ?_⟩
    · show is_model (part_valuation_of problem part tuple
        (fun private_variable => part_valuation (Sum.inr private_variable)))
        (problem.part_formula part)
      rw [part_valuation_of_private_eq problem part tuple part_valuation encodes]
      exact model
    · intro other _
      show is_model (part_valuation_of problem other tuple
        (fun private_variable => other_valuation other (Sum.inr private_variable)))
        (problem.part_formula other)
      rw [part_valuation_of_private_eq problem other tuple (other_valuation other)
        (other_encodes other)]
      exact other_model other
  refine ⟨global_valuation_of problem tuple
    (Function.update
      (fun other private_variable => other_valuation other (Sum.inr private_variable))
      part (fun private_variable => part_valuation (Sum.inr private_variable))), ?_,
    fun _ _ => rfl, ?_⟩
  · rw [is_model_conjunction_iff]
    intro other
    rw [global_valuation_of_rename]
    exact all_parts other
  · rw [global_valuation_of_rename, Function.update_self]
    exact part_valuation_of_private_eq problem part tuple part_valuation encodes

theorem composition_private_fixed_iff (problem : composition_problem original_count part_count)
    (exact : ∀ part, part_is_projection_exact problem part) (tuple : global_tuple problem)
    (satisfied : satisfies_all_parts problem tuple) (part : Fin part_count)
    (chosen : problem.private_type part → Prop) :
    private_fixed_in_conjunction problem tuple part chosen ↔
      private_fixed_in_part problem part (restrict_to_part problem tuple part) chosen := by
  constructor
  · intro fixed first second first_model first_encodes second_model second_encodes
      private_variable is_chosen
    obtain ⟨first_global, first_global_model, first_global_encodes, first_restricts⟩ :=
      part_model_extends problem exact tuple satisfied part first first_model first_encodes
    obtain ⟨second_global, second_global_model, second_global_encodes, second_restricts⟩ :=
      part_model_extends problem exact tuple satisfied part second second_model second_encodes
    have agree := fixed first_global second_global first_global_model first_global_encodes
      second_global_model second_global_encodes private_variable is_chosen
    rw [← first_restricts, ← second_restricts]
    exact agree
  · intro fixed first second first_model first_encodes second_model second_encodes
      private_variable is_chosen
    obtain ⟨first_part_model, first_part_encodes⟩ :=
      conjunction_model_restricts problem first first_model tuple first_encodes part
    obtain ⟨second_part_model, second_part_encodes⟩ :=
      conjunction_model_restricts problem second second_model tuple second_encodes part
    exact fixed _ _ first_part_model first_part_encodes second_part_model second_part_encodes
      private_variable is_chosen

theorem models_encoding_agree_on_shared (problem : composition_problem original_count part_count)
    (tuple : global_tuple problem) (first second : global_variable problem → Bool)
    (first_encodes : global_encodes problem first tuple)
    (second_encodes : global_encodes problem second tuple)
    (shared_variable : Σ original, problem.block_type original) :
    first (Sum.inl shared_variable) = second (Sum.inl shared_variable) := by
  obtain ⟨original, block_variable⟩ := shared_variable
  exact (first_encodes original block_variable).trans (second_encodes original block_variable).symm

theorem tuples_equal_of_agree_on_shared (problem : composition_problem original_count part_count)
    (first second : global_variable problem → Bool)
    (first_tuple second_tuple : global_tuple problem)
    (first_encodes : global_encodes problem first first_tuple)
    (second_encodes : global_encodes problem second second_tuple)
    (agree : ∀ shared_variable : Σ original, problem.block_type original,
      first (Sum.inl shared_variable) = second (Sum.inl shared_variable)) :
    first_tuple = second_tuple := by
  funext original
  apply problem.block_code_injective original
  funext block_variable
  exact (first_encodes original block_variable).symm.trans
    ((agree ⟨original, block_variable⟩).trans (second_encodes original block_variable))

theorem composition_shared_projected_count
    (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part) :
    projected_count (conjunction_formula problem)
        (composition_kept_variables problem fun _ => ∅) =
      (Finset.univ.filter (satisfies_all_parts problem)).card := by
  obtain ⟨model_tuple, tuple_model⟩ := composition_projection_exact problem covers exact
  unfold projected_count projected_models model_set
  symm
  refine Finset.card_bij
    (fun tuple _ => masked_restriction (composition_kept_variables problem fun _ => ∅)
      (global_valuation_of problem tuple fun _ _ => false)) ?_ ?_ ?_
  · intro tuple tuple_mem
    obtain ⟨valuation, model, encodes⟩ := tuple_model tuple (Finset.mem_filter.mp tuple_mem).2
    refine Finset.mem_image.mpr
      ⟨valuation, Finset.mem_filter.mpr ⟨Finset.mem_univ _, model⟩, ?_⟩
    apply (masked_restriction_eq_iff _ _ _).mpr
    intro variable_name kept
    obtain ⟨shared_variable, rfl⟩ := shared_of_mem_no_private problem variable_name kept
    exact models_encoding_agree_on_shared problem tuple _ _ encodes (fun _ _ => rfl)
      shared_variable
  · intro first _ second _ same_pattern
    refine tuples_equal_of_agree_on_shared problem
      (global_valuation_of problem first fun _ _ => false)
      (global_valuation_of problem second fun _ _ => false) first second (fun _ _ => rfl)
      (fun _ _ => rfl) ?_
    intro shared_variable
    exact (masked_restriction_eq_iff _ _ _).mp same_pattern _
      (shared_mem_composition_kept problem _ shared_variable)
  · intro pattern pattern_mem
    obtain ⟨valuation, valuation_mem, rfl⟩ := Finset.mem_image.mp pattern_mem
    obtain ⟨tuple, satisfied, encodes⟩ :=
      model_tuple valuation (Finset.mem_filter.mp valuation_mem).2
    refine ⟨tuple, Finset.mem_filter.mpr ⟨Finset.mem_univ _, satisfied⟩, ?_⟩
    apply (masked_restriction_eq_iff _ _ _).mpr
    intro variable_name kept
    obtain ⟨shared_variable, rfl⟩ := shared_of_mem_no_private problem variable_name kept
    exact models_encoding_agree_on_shared problem tuple _ _ (fun _ _ => rfl) encodes
      shared_variable

theorem composition_keep_private_iff (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part)
    (kept_private : ∀ part, Finset (problem.private_type part)) :
    projected_count (conjunction_formula problem)
        (composition_kept_variables problem kept_private) =
        (Finset.univ.filter (satisfies_all_parts problem)).card ↔
      ∀ tuple, satisfies_all_parts problem tuple → ∀ part,
        private_fixed_in_part problem part (restrict_to_part problem tuple part)
          (fun private_variable => private_variable ∈ kept_private part) := by
  rw [← composition_shared_projected_count problem covers exact]
  have subset : composition_kept_variables problem (fun _ => ∅) ⊆
      composition_kept_variables problem kept_private := by
    intro variable_name kept
    obtain ⟨shared_variable, rfl⟩ := shared_of_mem_no_private problem variable_name kept
    exact shared_mem_composition_kept problem kept_private shared_variable
  unfold projected_count
  refine (eq_comm.trans
    (projected_card_eq_iff (model_set (conjunction_formula problem)) _ _ subset)).trans ?_
  constructor
  · intro agree tuple satisfied part
    refine (composition_private_fixed_iff problem exact tuple satisfied part _).mp ?_
    intro first second first_model first_encodes second_model second_encodes
      private_variable is_kept
    refine agree first (Finset.mem_filter.mpr ⟨Finset.mem_univ _, first_model⟩) second
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, second_model⟩) ?_ _
      ((private_mem_composition_kept_iff problem kept_private part private_variable).mpr is_kept)
    intro variable_name kept
    obtain ⟨shared_variable, rfl⟩ := shared_of_mem_no_private problem variable_name kept
    exact models_encoding_agree_on_shared problem tuple first second first_encodes
      second_encodes shared_variable
  · intro fixed first first_mem second second_mem agree_shared variable_name kept
    have first_model := (Finset.mem_filter.mp first_mem).2
    have second_model := (Finset.mem_filter.mp second_mem).2
    obtain ⟨first_tuple, first_satisfied, first_encodes⟩ :=
      model_has_global_tuple problem covers exact first first_model
    obtain ⟨second_tuple, _, second_encodes⟩ :=
      model_has_global_tuple problem covers exact second second_model
    have same_tuple : first_tuple = second_tuple :=
      tuples_equal_of_agree_on_shared problem first second first_tuple second_tuple
        first_encodes second_encodes
        (fun shared_variable => agree_shared _
          (shared_mem_composition_kept problem _ shared_variable))
    rw [← same_tuple] at second_encodes
    rcases variable_name with shared_variable | ⟨part, private_variable⟩
    · exact agree_shared _ (shared_mem_composition_kept problem _ shared_variable)
    · exact (composition_private_fixed_iff problem exact first_tuple first_satisfied part _).mpr
        (fixed first_tuple first_satisfied part) first second first_model first_encodes
        second_model second_encodes private_variable
        ((private_mem_composition_kept_iff problem kept_private part private_variable).mp kept)

theorem composition_keep_private_of_parsimonious
    (problem : composition_problem original_count part_count)
    (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part)
    (parsimonious : model_count (conjunction_formula problem) =
      (Finset.univ.filter (satisfies_all_parts problem)).card)
    (kept_private : ∀ part, Finset (problem.private_type part)) :
    projected_count (conjunction_formula problem)
        (composition_kept_variables problem kept_private) =
      (Finset.univ.filter (satisfies_all_parts problem)).card := by
  apply le_antisymm
  · rw [← parsimonious, ← projected_count_univ]
    exact projected_card_le_of_subset _ _ _ (Finset.subset_univ _)
  · rw [← composition_shared_projected_count problem covers exact]
    refine projected_card_le_of_subset _ _ _ ?_
    intro variable_name kept
    obtain ⟨shared_variable, rfl⟩ := shared_of_mem_no_private problem variable_name kept
    exact shared_mem_composition_kept problem kept_private shared_variable

end abstract_block_test

section linked_block_test

variable {domain_size : Fin original_count → ℕ}

def linked_kept_private (parts : Fin part_count → linked_part domain_size)
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    ∀ part, Finset ((linked_problem parts).private_type part) :=
  fun part => (Finset.univ : Finset (part_private_variable (parts part))).filter
    fun private_variable =>
      block_owner (parts part).csp (parts part).ladder_on private_variable.val ∈ kept_hidden part

def linked_kept_variables (parts : Fin part_count → linked_part domain_size)
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    Finset (global_variable (linked_problem parts)) :=
  composition_kept_variables (linked_problem parts) (linked_kept_private parts kept_hidden)

theorem linked_part_block_fixed_iff (parts : Fin part_count → linked_part domain_size)
    (part : Fin part_count) (blocks : fixes_blocks (parts part))
    (tuple : part_tuple (linked_problem parts) part) (h : Fin (parts part).vertex_count) :
    private_fixed_in_part (linked_problem parts) part tuple
        (fun private_variable : part_private_variable (parts part) =>
          block_owner (parts part).csp (parts part).ladder_on private_variable.val = h) ↔
      block_fixed_by_tuple (parts part).csp (parts part).originals
        (block_owner (parts part).csp (parts part).ladder_on) (parts part).formula
        (encodes_tuple (parts part).csp (parts part).originals (parts part).ladder_on)
        (concrete_tuple (parts part) tuple) h := by
  constructor
  · intro fixed first second first_model first_encodes second_model second_encodes
      variable_name owner_is
    by_cases original_h : (parts part).originals h = true
    · refine exactly_one_models_agree_on_originals (parts part).csp (parts part).originals
        (parts part).ladder_on first second (concrete_tuple (parts part) tuple)
        (blocks first first_model) (blocks second second_model) first_encodes second_encodes
        variable_name ?_
      rw [owner_is]
      exact original_h
    · have hidden_owner : (parts part).originals
          (block_owner (parts part).csp (parts part).ladder_on variable_name) = false := by
        rw [owner_is]
        exact Bool.eq_false_iff.mpr original_h
      have lift : ∀ concrete : boolean_variable (parts part).csp (parts part).ladder_on → Bool,
          is_model concrete (parts part).formula →
          encodes_tuple (parts part).csp (parts part).originals (parts part).ladder_on concrete
            (concrete_tuple (parts part) tuple) →
          is_model (concrete ∘ of_part_variable (parts part))
              ((linked_problem parts).part_formula part) ∧
            part_encodes (linked_problem parts) part (concrete ∘ of_part_variable (parts part))
              tuple := by
        intro concrete concrete_model concrete_encodes
        have round_trip :
            (concrete ∘ of_part_variable (parts part)) ∘ to_part_variable (parts part) =
              concrete := (valuation_equiv (parts part)).right_inv concrete
        have lifted_model : is_model
            ((concrete ∘ of_part_variable (parts part)) ∘ to_part_variable (parts part))
            (parts part).formula := by
          rw [round_trip]
          exact concrete_model
        have lifted_encodes : encodes_tuple (parts part).csp (parts part).originals
            (parts part).ladder_on
            ((concrete ∘ of_part_variable (parts part)) ∘ to_part_variable (parts part))
            (concrete_tuple (parts part) tuple) := by
          rw [round_trip]
          exact concrete_encodes
        exact ⟨(linked_part_formula_model_iff parts part _).mpr lifted_model,
          (linked_encodes_iff (parts part) _ (blocks _ lifted_model) tuple).mpr lifted_encodes⟩
      obtain ⟨first_lifted_model, first_lifted_encodes⟩ := lift first first_model first_encodes
      obtain ⟨second_lifted_model, second_lifted_encodes⟩ :=
        lift second second_model second_encodes
      exact fixed _ _ first_lifted_model first_lifted_encodes second_lifted_model
        second_lifted_encodes ⟨variable_name, hidden_owner⟩ owner_is
  · intro fixed first second first_model first_encodes second_model second_encodes
    rintro ⟨variable_name, hidden⟩ owner_is
    have first_concrete := (linked_part_formula_model_iff parts part first).mp first_model
    have second_concrete := (linked_part_formula_model_iff parts part second).mp second_model
    have agree : first (to_part_variable (parts part) variable_name) =
        second (to_part_variable (parts part) variable_name) :=
      fixed _ _ first_concrete
        ((linked_encodes_iff (parts part) first (blocks _ first_concrete) tuple).mp first_encodes)
        second_concrete
        ((linked_encodes_iff (parts part) second (blocks _ second_concrete) tuple).mp
          second_encodes)
        variable_name owner_is
    rw [to_part_variable_private (parts part) variable_name hidden] at agree
    exact agree

theorem linked_block_fixed_iff (parts : Fin part_count → linked_part domain_size)
    (exact : ∀ part, is_exact_part (parts part)) (tuple : global_tuple (linked_problem parts))
    (satisfied : satisfies_all_parts (linked_problem parts) tuple) (part : Fin part_count)
    (h : Fin (parts part).vertex_count) :
    private_fixed_in_conjunction (linked_problem parts) tuple part
        (fun private_variable : part_private_variable (parts part) =>
          block_owner (parts part).csp (parts part).ladder_on private_variable.val = h) ↔
      block_fixed_by_tuple (parts part).csp (parts part).originals
        (block_owner (parts part).csp (parts part).ladder_on) (parts part).formula
        (encodes_tuple (parts part).csp (parts part).originals (parts part).ladder_on)
        (tuple_on_part (parts part) tuple) h :=
  (composition_private_fixed_iff (linked_problem parts)
    (fun part => linked_part_is_projection_exact parts part (exact part)) tuple satisfied part
    _).trans (linked_part_block_fixed_iff parts part (exact part).1 _ h)

theorem linked_keep_blocks_iff (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part))
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    projected_count (conjunction_formula (linked_problem parts))
        (linked_kept_variables parts kept_hidden) =
        (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card ↔
      ∀ tuple, satisfies_all_parts (linked_problem parts) tuple → ∀ part,
        ∀ h ∈ kept_hidden part, block_fixed_by_tuple (parts part).csp (parts part).originals
          (block_owner (parts part).csp (parts part).ladder_on) (parts part).formula
          (encodes_tuple (parts part).csp (parts part).originals (parts part).ladder_on)
          (tuple_on_part (parts part) tuple) h := by
  unfold linked_kept_variables
  rw [composition_keep_private_iff (linked_problem parts) covers
    (fun part => linked_part_is_projection_exact parts part (exact part))]
  refine forall_congr' fun tuple => imp_congr_right fun _ => forall_congr' fun part => ?_
  constructor
  · intro fixed h h_kept
    refine (linked_part_block_fixed_iff parts part (exact part).1 _ h).mp ?_
    intro first second first_model first_encodes second_model second_encodes private_variable
      owner_is
    subst owner_is
    exact fixed first second first_model first_encodes second_model second_encodes
      private_variable (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_kept⟩)
  · intro fixed first second first_model first_encodes second_model second_encodes
      private_variable is_kept
    have owner_kept : block_owner (parts part).csp (parts part).ladder_on private_variable.val ∈
        kept_hidden part := (Finset.mem_filter.mp is_kept).2
    exact (linked_part_block_fixed_iff parts part (exact part).1 _ _).mpr
      (fixed _ owner_kept) first second first_model first_encodes second_model second_encodes
      private_variable rfl

theorem linked_keep_blocks_of_parsimonious (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part))
    (parsimonious : model_count (conjunction_formula (linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card)
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    projected_count (conjunction_formula (linked_problem parts))
        (linked_kept_variables parts kept_hidden) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card :=
  composition_keep_private_of_parsimonious (linked_problem parts) covers
    (fun part => linked_part_is_projection_exact parts part (exact part)) parsimonious _

def is_block_test (data : linked_part domain_size)
    (test : original_tuple data.csp data.originals → Fin data.vertex_count → Prop) : Prop :=
  ∀ tuple, in_relation data.csp data.originals tuple → ∀ h,
    (block_fixed_by_tuple data.csp data.originals (block_owner data.csp data.ladder_on)
      data.formula (encodes_tuple data.csp data.originals data.ladder_on) tuple h ↔ test tuple h)

theorem linked_keep_blocks_iff_tests (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part))
    (tests : ∀ part, original_tuple (parts part).csp (parts part).originals →
      Fin (parts part).vertex_count → Prop)
    (tests_hold : ∀ part, is_block_test (parts part) (tests part))
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    projected_count (conjunction_formula (linked_problem parts))
        (linked_kept_variables parts kept_hidden) =
        (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card ↔
      ∀ tuple, satisfies_all_parts (linked_problem parts) tuple → ∀ part,
        ∀ h ∈ kept_hidden part, tests part (tuple_on_part (parts part) tuple) h := by
  rw [linked_keep_blocks_iff parts covers exact kept_hidden]
  refine forall_congr' fun tuple => imp_congr_right fun satisfied => forall_congr' fun part =>
    forall_congr' fun h => imp_congr_right fun _ => ?_
  exact tests_hold part _ ((linked_satisfies_all_parts_iff parts tuple).mp satisfied part) h

end linked_block_test

section encoding_block_tests

variable {vertex_count : ℕ} {domain_size : Fin original_count → ℕ}

theorem support_part_block_test (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_block_test (support_part csp originals embed domain_match)
      (extensions_agree_on csp originals) :=
  fun tuple _ h => support_block_fixed_iff csp originals tuple h

theorem direct_part_block_test (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_block_test (direct_part csp originals embed domain_match)
      (extensions_agree_on csp originals) :=
  fun tuple _ h => direct_block_fixed_iff csp originals tuple h

theorem min_eo_part_block_test (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (listed : ∀ x, x ∈ order) (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_block_test (min_eo_part csp originals order embed domain_match)
      (extensions_agree_on csp originals) :=
  fun tuple _ h => block_fixed_iff_of_model_iff csp originals (min_eo_encoding csp order)
    (min_eo_any_graph_model_iff csp (earlier_in order)
      (keeps_one_direction_of_listing csp order listed)) tuple h

theorem partial_support_part_block_test (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_block_test (partial_support_part csp originals embed domain_match)
      (extensions_agree_on csp originals) :=
  fun tuple _ h => partial_support_block_fixed_iff csp originals tree has_original tuple h

theorem minimal_support_part_block_test (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_block_test (minimal_support_part csp originals order embed domain_match)
      (fun tuple h => ∃! a, in_upward_set csp originals order tuple h a) :=
  fun tuple in_rel h => minimal_support_block_fixed_iff csp originals order tree_order
    root_original tuple in_rel h

end encoding_block_tests

section log_block_test

variable {domain_size : Fin original_count → ℕ}

def log_linked_kept_private (parts : Fin part_count → log_linked_part domain_size)
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    ∀ part, Finset ((log_linked_problem parts).private_type part) :=
  fun part => (Finset.univ : Finset (log_part_private_variable (parts part))).filter
    fun private_variable => bit_owner (parts part).csp private_variable.val ∈ kept_hidden part

def log_linked_kept_variables (parts : Fin part_count → log_linked_part domain_size)
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    Finset (global_variable (log_linked_problem parts)) :=
  composition_kept_variables (log_linked_problem parts) (log_linked_kept_private parts kept_hidden)

theorem log_linked_part_block_fixed_iff (parts : Fin part_count → log_linked_part domain_size)
    (part : Fin part_count) (tuple : part_tuple (log_linked_problem parts) part)
    (h : Fin (parts part).vertex_count) :
    private_fixed_in_part (log_linked_problem parts) part tuple
        (fun private_variable : log_part_private_variable (parts part) =>
          bit_owner (parts part).csp private_variable.val = h) ↔
      block_fixed_by_tuple (parts part).csp (parts part).originals (bit_owner (parts part).csp)
        (log_encoding (parts part).csp) (log_encodes_tuple (parts part).csp (parts part).originals)
        (log_concrete_tuple (parts part) tuple) h := by
  constructor
  · intro fixed first second first_model first_encodes second_model second_encodes
      variable_name owner_is
    by_cases original_h : (parts part).originals h = true
    · refine (log_original_coding (parts part).csp (parts part).originals).2.2.1 first second
        (log_concrete_tuple (parts part) tuple) first_model first_encodes second_model
        second_encodes variable_name ?_
      rw [owner_is]
      exact original_h
    · have hidden_owner : (parts part).originals variable_name.1 = false := by
        have owner_h : variable_name.1 = h := owner_is
        rw [owner_h]
        exact Bool.eq_false_iff.mpr original_h
      have lift : ∀ concrete : log_variable (parts part).csp → Bool,
          is_model concrete (log_encoding (parts part).csp) →
          log_encodes_tuple (parts part).csp (parts part).originals concrete
            (log_concrete_tuple (parts part) tuple) →
          is_model (concrete ∘ of_log_part_variable (parts part))
              ((log_linked_problem parts).part_formula part) ∧
            part_encodes (log_linked_problem parts) part
              (concrete ∘ of_log_part_variable (parts part)) tuple := by
        intro concrete concrete_model concrete_encodes
        have round_trip :
            (concrete ∘ of_log_part_variable (parts part)) ∘ to_log_part_variable (parts part) =
              concrete := (log_valuation_equiv (parts part)).right_inv concrete
        have lifted_model : is_model
            ((concrete ∘ of_log_part_variable (parts part)) ∘ to_log_part_variable (parts part))
            (log_encoding (parts part).csp) := by
          rw [round_trip]
          exact concrete_model
        have lifted_encodes : log_encodes_tuple (parts part).csp (parts part).originals
            ((concrete ∘ of_log_part_variable (parts part)) ∘ to_log_part_variable (parts part))
            (log_concrete_tuple (parts part) tuple) := by
          rw [round_trip]
          exact concrete_encodes
        exact ⟨(log_linked_part_formula_model_iff parts part _).mpr lifted_model,
          (log_linked_encodes_iff (parts part) _ tuple).mpr lifted_encodes⟩
      obtain ⟨first_lifted_model, first_lifted_encodes⟩ := lift first first_model first_encodes
      obtain ⟨second_lifted_model, second_lifted_encodes⟩ :=
        lift second second_model second_encodes
      exact fixed _ _ first_lifted_model first_lifted_encodes second_lifted_model
        second_lifted_encodes ⟨variable_name, hidden_owner⟩ owner_is
  · intro fixed first second first_model first_encodes second_model second_encodes
    rintro ⟨variable_name, hidden⟩ owner_is
    have first_concrete := (log_linked_part_formula_model_iff parts part first).mp first_model
    have second_concrete := (log_linked_part_formula_model_iff parts part second).mp second_model
    have agree : first (to_log_part_variable (parts part) variable_name) =
        second (to_log_part_variable (parts part) variable_name) :=
      fixed _ _ first_concrete
        ((log_linked_encodes_iff (parts part) first tuple).mp first_encodes) second_concrete
        ((log_linked_encodes_iff (parts part) second tuple).mp second_encodes)
        variable_name owner_is
    rw [to_log_part_variable_private (parts part) variable_name hidden] at agree
    exact agree

theorem log_linked_block_fixed_iff (parts : Fin part_count → log_linked_part domain_size)
    (tuple : global_tuple (log_linked_problem parts))
    (satisfied : satisfies_all_parts (log_linked_problem parts) tuple) (part : Fin part_count)
    (h : Fin (parts part).vertex_count) :
    private_fixed_in_conjunction (log_linked_problem parts) tuple part
        (fun private_variable : log_part_private_variable (parts part) =>
          bit_owner (parts part).csp private_variable.val = h) ↔
      extensions_agree_on (parts part).csp (parts part).originals
        (log_tuple_on_part (parts part) tuple) h :=
  ((composition_private_fixed_iff (log_linked_problem parts)
    (fun part => log_linked_part_is_projection_exact parts part) tuple satisfied part _).trans
    (log_linked_part_block_fixed_iff parts part _ h)).trans
    (log_block_fixed_iff (parts part).csp (parts part).originals _ h)

theorem log_composition_keep_blocks_iff (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts))
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    projected_count (conjunction_formula (log_linked_problem parts))
        (log_linked_kept_variables parts kept_hidden) =
        (Finset.univ.filter (satisfies_all_parts (log_linked_problem parts))).card ↔
      ∀ tuple, satisfies_all_parts (log_linked_problem parts) tuple → ∀ part,
        ∀ h ∈ kept_hidden part, extensions_agree_on (parts part).csp (parts part).originals
          (log_tuple_on_part (parts part) tuple) h := by
  unfold log_linked_kept_variables
  rw [composition_keep_private_iff (log_linked_problem parts) covers
    (fun part => log_linked_part_is_projection_exact parts part)]
  refine forall_congr' fun tuple => imp_congr_right fun _ => forall_congr' fun part => ?_
  constructor
  · intro fixed h h_kept
    refine (log_block_fixed_iff (parts part).csp (parts part).originals _ h).mp
      ((log_linked_part_block_fixed_iff parts part _ h).mp ?_)
    intro first second first_model first_encodes second_model second_encodes private_variable
      owner_is
    subst owner_is
    exact fixed first second first_model first_encodes second_model second_encodes
      private_variable (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_kept⟩)
  · intro fixed first second first_model first_encodes second_model second_encodes
      private_variable is_kept
    have owner_kept : bit_owner (parts part).csp private_variable.val ∈ kept_hidden part :=
      (Finset.mem_filter.mp is_kept).2
    exact (log_linked_part_block_fixed_iff parts part _ _).mpr
      ((log_block_fixed_iff (parts part).csp (parts part).originals _ _).mpr
        (fixed _ owner_kept)) first second first_model first_encodes second_model
      second_encodes private_variable rfl

theorem log_composition_keep_blocks_of_parsimonious
    (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts))
    (parsimonious : model_count (conjunction_formula (log_linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (log_linked_problem parts))).card)
    (kept_hidden : ∀ part, Finset (Fin (parts part).vertex_count)) :
    projected_count (conjunction_formula (log_linked_problem parts))
        (log_linked_kept_variables parts kept_hidden) =
      (Finset.univ.filter (satisfies_all_parts (log_linked_problem parts))).card :=
  composition_keep_private_of_parsimonious (log_linked_problem parts) covers
    (fun part => log_linked_part_is_projection_exact parts part) parsimonious _

end log_block_test

namespace counterexamples

theorem ms_block_varies_alone :
    projected_count (minimal_support_encoding ms_part_csp middle_vertex_is_hidden [0, 1, 2])
        (owned_variables (block_owner ms_part_csp middle_vertex_is_hidden)
          (original_vertices middle_vertex_is_hidden ∪ {1})) = 3 ∧
      relation_count ms_part_csp middle_vertex_is_hidden = 2 := by
  decide +kernel

theorem ms_block_test_fails_alone :
    ¬ ∀ tuple, in_relation ms_part_csp middle_vertex_is_hidden tuple →
      ∀ h ∈ ({1} : Finset (Fin 3)),
        ∃! a, in_upward_set ms_part_csp middle_vertex_is_hidden [0, 1, 2] tuple h a := by
  intro all_fixed
  have same_count := (minimal_support_keep_blocks_iff ms_part_csp middle_vertex_is_hidden
    [0, 1, 2] ms_part_counts.1 (by decide +kernel) {1}).mpr all_fixed
  rw [ms_block_varies_alone.1, ms_block_varies_alone.2] at same_count
  exact absurd same_count (by decide)

theorem ms_block_fixed_in_composition :
    projected_count (conjunction_formula (linked_problem ms_composition_parts))
        (linked_kept_variables ms_composition_parts fun _ => Finset.univ) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem ms_composition_parts))).card :=
  linked_keep_blocks_of_parsimonious ms_composition_parts ms_composition_covers
    ms_composition_exact (ms_composition_counts.2.trans ms_composition_counts.1.symm) _

theorem ms_block_test_holds_in_composition :
    ∀ tuple, satisfies_all_parts (linked_problem ms_composition_parts) tuple → ∀ h : Fin 3,
      ∃! a, in_upward_set ms_part_csp middle_vertex_is_hidden [0, 1, 2]
        (tuple_on_part (ms_composition_parts 0) tuple) h a := by
  intro tuple satisfied h
  have fixed := (linked_keep_blocks_iff ms_composition_parts ms_composition_covers
    ms_composition_exact (fun _ => Finset.univ)).mp ms_block_fixed_in_composition tuple satisfied
    0 h (Finset.mem_univ h)
  exact (minimal_support_block_fixed_iff ms_part_csp middle_vertex_is_hidden [0, 1, 2]
    ms_part_counts.1 (by decide +kernel) _
    ((linked_satisfies_all_parts_iff ms_composition_parts tuple).mp satisfied 0) h).mp fixed

theorem conjunction_block_varies_alone :
    relation_count conjunction_part_csp first_vertex_is_original = 2 ∧
      projected_count (support_encoding conjunction_part_csp)
        (owned_variables (block_owner conjunction_part_csp all_vertices)
          (original_vertices first_vertex_is_original ∪ {1})) = 3 ∧
      projected_count (direct_encoding conjunction_part_csp)
        (owned_variables (block_owner conjunction_part_csp all_vertices)
          (original_vertices first_vertex_is_original ∪ {1})) = 3 ∧
      projected_count (min_eo_encoding conjunction_part_csp [0, 1])
        (owned_variables (block_owner conjunction_part_csp all_vertices)
          (original_vertices first_vertex_is_original ∪ {1})) = 3 ∧
      projected_count (partial_support_encoding conjunction_part_csp first_vertex_is_original)
        (owned_variables (block_owner conjunction_part_csp first_vertex_is_original)
          (original_vertices first_vertex_is_original ∪ {1})) = 4 ∧
      projected_count (log_encoding conjunction_part_csp)
        (owned_variables (bit_owner conjunction_part_csp)
          (original_vertices first_vertex_is_original ∪ {1})) = 3 := by
  decide +kernel

theorem conjunction_extensions_disagree_alone :
    ¬ ∀ tuple, in_relation conjunction_part_csp first_vertex_is_original tuple →
      ∀ h ∈ ({1} : Finset (Fin 2)),
        extensions_agree_on conjunction_part_csp first_vertex_is_original tuple h := by
  intro all_agree
  have same_count := (support_keep_blocks_iff conjunction_part_csp first_vertex_is_original
    {1}).mpr all_agree
  rw [conjunction_block_varies_alone.2.1, conjunction_block_varies_alone.1] at same_count
  exact absurd same_count (by decide)

theorem conjunction_support_blocks_fixed_in_composition :
    projected_count (conjunction_formula (linked_problem conjunction_support_parts))
        (linked_kept_variables conjunction_support_parts fun _ => Finset.univ) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem conjunction_support_parts))).card := by
  decide +kernel

theorem conjunction_direct_blocks_fixed_in_composition :
    projected_count (conjunction_formula (linked_problem conjunction_direct_parts))
        (linked_kept_variables conjunction_direct_parts fun _ => Finset.univ) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem conjunction_direct_parts))).card := by
  decide +kernel

theorem conjunction_min_eo_blocks_fixed_in_composition :
    projected_count (conjunction_formula (linked_problem conjunction_min_eo_parts))
        (linked_kept_variables conjunction_min_eo_parts fun _ => Finset.univ) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem conjunction_min_eo_parts))).card := by
  decide +kernel

theorem conjunction_partial_support_blocks_fixed_in_composition :
    projected_count (conjunction_formula (linked_problem conjunction_partial_support_parts))
        (linked_kept_variables conjunction_partial_support_parts fun _ => Finset.univ) =
      (Finset.univ.filter
        (satisfies_all_parts (linked_problem conjunction_partial_support_parts))).card := by
  decide +kernel

theorem conjunction_log_blocks_fixed_in_composition :
    projected_count (conjunction_formula (log_linked_problem conjunction_log_parts))
        (log_linked_kept_variables conjunction_log_parts fun _ => Finset.univ) =
      (Finset.univ.filter (satisfies_all_parts (log_linked_problem conjunction_log_parts))).card := by
  decide +kernel

theorem conjunction_support_composition_covers :
    covers_all_originals (linked_problem conjunction_support_parts) := by
  unfold covers_all_originals
  decide +kernel

theorem conjunction_support_composition_exact :
    ∀ part, is_exact_part (conjunction_support_parts part) := by
  intro part
  fin_cases part
  · exact support_part_is_exact conjunction_part_csp first_vertex_is_original conjunction_embed
      conjunction_domain_match
  · exact support_part_is_exact conjunction_restriction_csp all_vertices identity_embed
      conjunction_restriction_domain_match

theorem conjunction_support_test_holds_in_composition :
    ∀ tuple, satisfies_all_parts (linked_problem conjunction_support_parts) tuple → ∀ h : Fin 2,
      extensions_agree_on conjunction_part_csp first_vertex_is_original
        (tuple_on_part (conjunction_support_parts 0) tuple) h := by
  intro tuple satisfied h
  have fixed := (linked_keep_blocks_iff conjunction_support_parts
    conjunction_support_composition_covers conjunction_support_composition_exact
    (fun _ => Finset.univ)).mp conjunction_support_blocks_fixed_in_composition tuple satisfied 0 h
    (Finset.mem_univ h)
  exact (support_block_fixed_iff conjunction_part_csp first_vertex_is_original _ h).mp fixed

theorem conjunction_log_test_holds_in_composition :
    ∀ tuple, satisfies_all_parts (log_linked_problem conjunction_log_parts) tuple → ∀ part,
      ∀ h : Fin (conjunction_log_parts part).vertex_count,
        extensions_agree_on (conjunction_log_parts part).csp (conjunction_log_parts part).originals
          (log_tuple_on_part (conjunction_log_parts part) tuple) h :=
  fun tuple satisfied part h => (log_composition_keep_blocks_iff conjunction_log_parts
    conjunction_log_composition_covers (fun _ => Finset.univ)).mp
    conjunction_log_blocks_fixed_in_composition tuple satisfied part h (Finset.mem_univ h)

end counterexamples

end parsimony
