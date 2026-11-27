import parsimony.partial_support
import parsimony.minimal_support
import parsimony.composition
import parsimony.dropping_blocks
import parsimony.min_eo_any_graph

namespace parsimony

variable {original_count part_count : ℕ}

abbrev ladder_block (size : ℕ) := Fin size ⊕ Fin (size - 1)

def ladder_block_code (size : ℕ) (value : Fin size) : ladder_block size → Bool
  | Sum.inl candidate => decide (candidate = value)
  | Sum.inr step => decide (step.val < value.val)

theorem ladder_block_code_injective (size : ℕ) :
    Function.Injective (ladder_block_code size) := by
  intro first second same
  have at_first := congrFun same (Sum.inl first)
  simp only [ladder_block_code] at at_first
  simpa using at_first

theorem fin_cast_eq_iff {first_size second_size : ℕ} (sizes_equal : first_size = second_size)
    (first : Fin first_size) (second : Fin second_size) :
    Fin.cast sizes_equal first = second ↔ first = Fin.cast sizes_equal.symm second := by
  constructor
  · intro same
    have same_value : (Fin.cast sizes_equal first).val = second.val := congrArg Fin.val same
    exact Fin.ext same_value
  · intro same
    have same_value : first.val = (Fin.cast sizes_equal.symm second).val := congrArg Fin.val same
    exact Fin.ext same_value

structure linked_part (domain_size : Fin original_count → ℕ) where
  vertex_count : ℕ
  csp : binary_csp vertex_count
  originals : Fin vertex_count → Bool
  ladder_on : Fin vertex_count → Bool
  ladder_covers : ∀ x, originals x = true → ladder_on x = true
  embed : original_vertex originals → Fin original_count
  domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)
  formula : cnf_formula (boolean_variable csp ladder_on)

section link

variable {domain_size : Fin original_count → ℕ}

abbrev part_private_variable (data : linked_part domain_size) :=
  {variable_name : boolean_variable data.csp data.ladder_on //
    data.originals (block_owner data.csp data.ladder_on variable_name) = false}

abbrev linked_part_variable (data : linked_part domain_size) :=
  (Σ member : original_vertex data.originals, ladder_block (domain_size (data.embed member))) ⊕
    part_private_variable data

def to_part_variable (data : linked_part domain_size) :
    boolean_variable data.csp data.ladder_on → linked_part_variable data
  | Sum.inl ⟨x, a⟩ =>
    if on_x : data.originals x = true then
      Sum.inl ⟨⟨x, on_x⟩, Sum.inl (Fin.cast (data.domain_match ⟨x, on_x⟩) a)⟩
    else Sum.inr ⟨Sum.inl ⟨x, a⟩, Bool.eq_false_iff.mpr on_x⟩
  | Sum.inr ⟨⟨x, ladder_x⟩, i⟩ =>
    if on_x : data.originals x = true then
      Sum.inl ⟨⟨x, on_x⟩,
        Sum.inr (Fin.cast (congrArg (fun size => size - 1) (data.domain_match ⟨x, on_x⟩)) i)⟩
    else Sum.inr ⟨Sum.inr ⟨⟨x, ladder_x⟩, i⟩, Bool.eq_false_iff.mpr on_x⟩

def of_part_variable (data : linked_part domain_size) :
    linked_part_variable data → boolean_variable data.csp data.ladder_on
  | Sum.inl ⟨member, Sum.inl value⟩ =>
    Sum.inl ⟨member.val, Fin.cast (data.domain_match member).symm value⟩
  | Sum.inl ⟨member, Sum.inr step⟩ =>
    Sum.inr ⟨⟨member.val, data.ladder_covers member.val member.property⟩,
      Fin.cast (congrArg (fun size => size - 1) (data.domain_match member)).symm step⟩
  | Sum.inr hidden_variable => hidden_variable.val

theorem to_part_variable_value (data : linked_part domain_size)
    (member : original_vertex data.originals) (a : Fin (data.csp.domain_size member.val)) :
    to_part_variable data (Sum.inl ⟨member.val, a⟩) =
      Sum.inl ⟨member, Sum.inl (Fin.cast (data.domain_match member) a)⟩ := by
  obtain ⟨x, on_x⟩ := member
  simp only [to_part_variable]
  split
  · rfl
  · contradiction

theorem to_part_variable_ladder (data : linked_part domain_size)
    (member : original_vertex data.originals) (ladder_member : data.ladder_on member.val = true)
    (i : Fin (data.csp.domain_size member.val - 1)) :
    to_part_variable data (Sum.inr ⟨⟨member.val, ladder_member⟩, i⟩) =
      Sum.inl ⟨member,
        Sum.inr (Fin.cast (congrArg (fun size => size - 1) (data.domain_match member)) i)⟩ := by
  obtain ⟨x, on_x⟩ := member
  simp only [to_part_variable]
  split
  · rfl
  · contradiction

theorem to_part_variable_private (data : linked_part domain_size)
    (variable_name : boolean_variable data.csp data.ladder_on)
    (hidden : data.originals (block_owner data.csp data.ladder_on variable_name) = false) :
    to_part_variable data variable_name = Sum.inr ⟨variable_name, hidden⟩ := by
  rcases variable_name with ⟨x, a⟩ | ⟨⟨x, ladder_x⟩, i⟩
  · change data.originals x = false at hidden
    simp only [to_part_variable]
    split
    · rename_i on_x
      exact absurd (hidden.symm.trans on_x) (by decide)
    · rfl
  · change data.originals x = false at hidden
    simp only [to_part_variable]
    split
    · rename_i on_x
      exact absurd (hidden.symm.trans on_x) (by decide)
    · rfl

theorem of_to_part_variable (data : linked_part domain_size)
    (variable_name : boolean_variable data.csp data.ladder_on) :
    of_part_variable data (to_part_variable data variable_name) = variable_name := by
  by_cases on_owner : data.originals (block_owner data.csp data.ladder_on variable_name) = true
  · rcases variable_name with ⟨x, a⟩ | ⟨⟨x, ladder_x⟩, i⟩
    · change data.originals x = true at on_owner
      rw [to_part_variable_value data ⟨x, on_owner⟩ a]
      rfl
    · change data.originals x = true at on_owner
      rw [to_part_variable_ladder data ⟨x, on_owner⟩ ladder_x i]
      rfl
  · rw [to_part_variable_private data variable_name (Bool.eq_false_iff.mpr on_owner)]
    rfl

theorem to_of_part_variable (data : linked_part domain_size)
    (part_variable_name : linked_part_variable data) :
    to_part_variable data (of_part_variable data part_variable_name) = part_variable_name := by
  rcases part_variable_name with ⟨member, value | step⟩ | ⟨variable_name, hidden⟩
  · show to_part_variable data
      (Sum.inl ⟨member.val, Fin.cast (data.domain_match member).symm value⟩) = _
    rw [to_part_variable_value]
    rfl
  · show to_part_variable data
      (Sum.inr ⟨⟨member.val, data.ladder_covers member.val member.property⟩,
        Fin.cast (congrArg (fun size => size - 1) (data.domain_match member)).symm step⟩) = _
    rw [to_part_variable_ladder]
    rfl
  · exact to_part_variable_private data variable_name hidden

def valuation_equiv (data : linked_part domain_size) :
    (linked_part_variable data → Bool) ≃ (boolean_variable data.csp data.ladder_on → Bool) where
  toFun := fun valuation => valuation ∘ to_part_variable data
  invFun := fun concrete => concrete ∘ of_part_variable data
  left_inv := fun valuation => by
    funext part_variable_name
    exact congrArg valuation (to_of_part_variable data part_variable_name)
  right_inv := fun concrete => by
    funext variable_name
    exact congrArg concrete (of_to_part_variable data variable_name)

def concrete_tuple (data : linked_part domain_size)
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    original_tuple data.csp data.originals :=
  fun member => Fin.cast (data.domain_match member).symm (tuple member)

def abstract_tuple (data : linked_part domain_size) (tuple : original_tuple data.csp data.originals) :
    ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member)) :=
  fun member => Fin.cast (data.domain_match member) (tuple member)

theorem concrete_abstract_tuple (data : linked_part domain_size)
    (tuple : original_tuple data.csp data.originals) :
    concrete_tuple data (abstract_tuple data tuple) = tuple := by
  funext member
  exact Fin.ext rfl

theorem abstract_concrete_tuple (data : linked_part domain_size)
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    abstract_tuple data (concrete_tuple data tuple) = tuple := by
  funext member
  exact Fin.ext rfl

def tuple_on_part (data : linked_part domain_size) (tuple : ∀ original, Fin (domain_size original)) :
    original_tuple data.csp data.originals :=
  fun member => Fin.cast (data.domain_match member).symm (tuple (data.embed member))

def linked_encodes (data : linked_part domain_size)
    (valuation : linked_part_variable data → Bool)
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    Prop :=
  ∀ member block_variable, valuation (Sum.inl ⟨member, block_variable⟩) =
    ladder_block_code (domain_size (data.embed member)) (tuple member) block_variable

theorem linked_encodes_iff (data : linked_part domain_size)
    (valuation : linked_part_variable data → Bool)
    (blocks : is_model (valuation ∘ to_part_variable data)
      (exactly_one_part data.csp data.ladder_on))
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    linked_encodes data valuation tuple ↔
      encodes_tuple data.csp data.originals data.ladder_on (valuation ∘ to_part_variable data)
        (concrete_tuple data tuple) := by
  constructor
  · intro encodes member a
    show valuation (to_part_variable data (Sum.inl ⟨member.val, a⟩)) =
      decide (a = concrete_tuple data tuple member)
    rw [to_part_variable_value, encodes member (Sum.inl (Fin.cast (data.domain_match member) a))]
    exact decide_eq_decide.mpr (fin_cast_eq_iff (data.domain_match member) a (tuple member))
  · intro encodes member block_variable
    have value_bits : ∀ a : Fin (data.csp.domain_size member.val),
        valuation (Sum.inl ⟨member, Sum.inl (Fin.cast (data.domain_match member) a)⟩) =
          decide (a = concrete_tuple data tuple member) := by
      intro a
      rw [← to_part_variable_value data member a]
      exact encodes member a
    rcases block_variable with value | step
    · obtain ⟨a, rfl⟩ : ∃ a, Fin.cast (data.domain_match member) a = value :=
        ⟨Fin.cast (data.domain_match member).symm value, Fin.ext rfl⟩
      rw [value_bits a]
      exact decide_eq_decide.mpr (fin_cast_eq_iff (data.domain_match member) a (tuple member)).symm
    · obtain ⟨i, rfl⟩ : ∃ i, Fin.cast (congrArg (fun size => size - 1) (data.domain_match member))
          i = step :=
        ⟨Fin.cast (congrArg (fun size => size - 1) (data.domain_match member)).symm step,
          Fin.ext rfl⟩
      obtain ⟨chosen, chosen_fixed⟩ :=
        (is_model_exactly_one_part_iff data.csp data.ladder_on _).mp blocks member.val
          (data.ladder_covers member.val member.property)
      have chosen_is : chosen = concrete_tuple data tuple member := by
        have at_chosen := chosen_fixed.1 chosen
        rw [encodes member chosen] at at_chosen
        simpa using at_chosen
      rw [← to_part_variable_ladder data member (data.ladder_covers member.val member.property) i]
      refine (chosen_fixed.2 i).trans ?_
      rw [chosen_is]
      rfl

def fixes_blocks (data : linked_part domain_size) : Prop :=
  ∀ valuation, is_model valuation data.formula →
    is_model valuation (exactly_one_part data.csp data.ladder_on)

def is_exact_part (data : linked_part domain_size) : Prop :=
  fixes_blocks data ∧
    is_projection_exact data.csp data.originals data.ladder_on data.formula

def linked_problem (parts : Fin part_count → linked_part domain_size) :
    composition_problem original_count part_count where
  domain_size := domain_size
  block_type := fun original => ladder_block (domain_size original)
  block_fintype := fun _ => inferInstance
  block_decidable_eq := fun _ => inferInstance
  block_code := fun original => ladder_block_code (domain_size original)
  block_code_injective := fun original => ladder_block_code_injective (domain_size original)
  scope_type := fun part => original_vertex (parts part).originals
  scope_fintype := fun _ => inferInstance
  scope_decidable_eq := fun _ => inferInstance
  scope_original := fun part => (parts part).embed
  private_type := fun part => part_private_variable (parts part)
  private_fintype := fun _ => inferInstance
  private_decidable_eq := fun _ => inferInstance
  part_formula := fun part => rename_formula (to_part_variable (parts part)) (parts part).formula
  part_relation := fun part tuple =>
    in_relation (parts part).csp (parts part).originals (concrete_tuple (parts part) tuple)
  part_relation_decidable := fun _ _ => inferInstance

theorem linked_part_formula_model_iff (parts : Fin part_count → linked_part domain_size)
    (part : Fin part_count) (valuation : part_variable (linked_problem parts) part → Bool) :
    is_model valuation ((linked_problem parts).part_formula part) ↔
      is_model (valuation ∘ to_part_variable (parts part)) (parts part).formula :=
  is_model_rename_formula_iff _ _ _

theorem linked_part_encodes_iff (parts : Fin part_count → linked_part domain_size)
    (part : Fin part_count) (valuation : part_variable (linked_problem parts) part → Bool)
    (tuple : part_tuple (linked_problem parts) part) :
    part_encodes (linked_problem parts) part valuation tuple ↔
      linked_encodes (parts part) valuation tuple :=
  Iff.rfl

theorem linked_part_relation_iff (parts : Fin part_count → linked_part domain_size)
    (part : Fin part_count) (tuple : part_tuple (linked_problem parts) part) :
    (linked_problem parts).part_relation part tuple ↔
      in_relation (parts part).csp (parts part).originals (concrete_tuple (parts part) tuple) :=
  Iff.rfl

theorem linked_satisfies_all_parts_iff (parts : Fin part_count → linked_part domain_size)
    (tuple : global_tuple (linked_problem parts)) :
    satisfies_all_parts (linked_problem parts) tuple ↔
      ∀ part, in_relation (parts part).csp (parts part).originals
        (tuple_on_part (parts part) tuple) :=
  Iff.rfl

theorem linked_covers_iff (parts : Fin part_count → linked_part domain_size) :
    covers_all_originals (linked_problem parts) ↔
      ∀ original, ∃ part, ∃ member : original_vertex (parts part).originals,
        (parts part).embed member = original :=
  Iff.rfl

theorem linked_global_encodes_iff (parts : Fin part_count → linked_part domain_size)
    (valuation : global_variable (linked_problem parts) → Bool)
    (tuple : ∀ original, Fin (domain_size original)) :
    global_encodes (linked_problem parts) valuation tuple ↔
      ∀ original : Fin original_count,
        (∀ value : Fin (domain_size original),
          valuation (Sum.inl ⟨original, Sum.inl value⟩) = decide (value = tuple original)) ∧
        ∀ step : Fin (domain_size original - 1),
          valuation (Sum.inl ⟨original, Sum.inr step⟩) =
            decide (step.val < (tuple original).val) := by
  constructor
  · intro encodes original
    exact ⟨fun value => encodes original (Sum.inl value),
      fun step => encodes original (Sum.inr step)⟩
  · intro encodes original block_variable
    rcases block_variable with value | step
    · exact (encodes original).1 value
    · exact (encodes original).2 step

theorem linked_part_models_over (parts : Fin part_count → linked_part domain_size)
    (part : Fin part_count) (blocks : fixes_blocks (parts part))
    (tuple : part_tuple (linked_problem parts) part) :
    part_models_over (linked_problem parts) part tuple =
      models_over_tuple (parts part).csp (parts part).originals (parts part).ladder_on
        (parts part).formula (concrete_tuple (parts part) tuple) := by
  unfold part_models_over models_over_tuple
  refine Fintype.card_congr (Equiv.subtypeEquiv (valuation_equiv (parts part)) ?_)
  intro valuation
  have model_iff := linked_part_formula_model_iff parts part valuation
  constructor
  · rintro ⟨model, encodes⟩
    have concrete_model := model_iff.mp model
    exact ⟨concrete_model,
      (linked_encodes_iff (parts part) valuation (blocks _ concrete_model) tuple).mp encodes⟩
  · rintro ⟨concrete_model, encodes⟩
    exact ⟨model_iff.mpr concrete_model,
      (linked_encodes_iff (parts part) valuation (blocks _ concrete_model) tuple).mpr encodes⟩

theorem linked_part_is_projection_exact (parts : Fin part_count → linked_part domain_size)
    (part : Fin part_count) (exact : is_exact_part (parts part)) :
    part_is_projection_exact (linked_problem parts) part := by
  obtain ⟨blocks, projection_exact⟩ := exact
  constructor
  · intro valuation model
    have concrete_model := (linked_part_formula_model_iff parts part valuation).mp model
    obtain ⟨tuple, in_rel, encodes⟩ := projection_exact.1 _ concrete_model
    refine ⟨abstract_tuple (parts part) tuple, ?_, ?_⟩
    · show in_relation (parts part).csp (parts part).originals
        (concrete_tuple (parts part) (abstract_tuple (parts part) tuple))
      rw [concrete_abstract_tuple]
      exact in_rel
    · refine (linked_encodes_iff (parts part) valuation (blocks _ concrete_model) _).mpr ?_
      rw [concrete_abstract_tuple]
      exact encodes
  · intro tuple in_rel
    have concrete_in_rel : in_relation (parts part).csp (parts part).originals
        (concrete_tuple (parts part) tuple) := in_rel
    obtain ⟨concrete, concrete_model, encodes⟩ := projection_exact.2 _ concrete_in_rel
    have round_trip : (concrete ∘ of_part_variable (parts part)) ∘ to_part_variable (parts part) =
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
      exact encodes
    exact ⟨concrete ∘ of_part_variable (parts part),
      (linked_part_formula_model_iff parts part _).mpr lifted_model,
      (linked_encodes_iff (parts part) _ (blocks _ lifted_model) tuple).mpr lifted_encodes⟩

theorem linked_composition_model_count (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) :
    model_count (conjunction_formula (linked_problem parts)) =
      ∑ tuple ∈ Finset.univ.filter (satisfies_all_parts (linked_problem parts)),
        ∏ part, models_over_tuple (parts part).csp (parts part).originals (parts part).ladder_on
          (parts part).formula (tuple_on_part (parts part) tuple) := by
  rw [composition_model_count (linked_problem parts) covers
    (fun part => linked_part_is_projection_exact parts part (exact part))]
  refine Finset.sum_congr rfl fun tuple _ => Finset.prod_congr rfl fun part _ => ?_
  exact linked_part_models_over parts part (exact part).1 _

theorem linked_composition_factor_positive (parts : Fin part_count → linked_part domain_size)
    (exact : ∀ part, is_exact_part (parts part)) (tuple : global_tuple (linked_problem parts))
    (satisfied : satisfies_all_parts (linked_problem parts) tuple) (part : Fin part_count) :
    0 < models_over_tuple (parts part).csp (parts part).originals (parts part).ladder_on
      (parts part).formula (tuple_on_part (parts part) tuple) := by
  have positive := composition_factor_positive (linked_problem parts)
    (fun part => linked_part_is_projection_exact parts part (exact part)) tuple satisfied part
  rw [linked_part_models_over parts part (exact part).1] at positive
  exact positive

theorem linked_composition_projection_exact (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) :
    (∀ valuation, is_model valuation (conjunction_formula (linked_problem parts)) →
      ∃ tuple, satisfies_all_parts (linked_problem parts) tuple ∧
        global_encodes (linked_problem parts) valuation tuple) ∧
    (∀ tuple, satisfies_all_parts (linked_problem parts) tuple →
      ∃ valuation, is_model valuation (conjunction_formula (linked_problem parts)) ∧
        global_encodes (linked_problem parts) valuation tuple) :=
  composition_projection_exact (linked_problem parts) covers
    (fun part => linked_part_is_projection_exact parts part (exact part))

theorem linked_composition_parsimonious_iff (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part)) :
    model_count (conjunction_formula (linked_problem parts)) =
        (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card ↔
      ∀ tuple, satisfies_all_parts (linked_problem parts) tuple →
        ∀ part, models_over_tuple (parts part).csp (parts part).originals (parts part).ladder_on
          (parts part).formula (tuple_on_part (parts part) tuple) = 1 := by
  rw [composition_parsimonious_iff (linked_problem parts) covers
    (fun part => linked_part_is_projection_exact parts part (exact part))]
  refine forall_congr' fun tuple => imp_congr_right fun _ => forall_congr' fun part => ?_
  have same := linked_part_models_over parts part (exact part).1
    (restrict_to_part (linked_problem parts) tuple part)
  constructor
  · intro count_one
    exact same.symm.trans count_one
  · intro count_one
    exact same.trans count_one

theorem models_over_tuple_eq_one_iff {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (formula : cnf_formula (boolean_variable csp ladder_on))
    (tuple : original_tuple csp originals) :
    models_over_tuple csp originals ladder_on formula tuple = 1 ↔
      ∃! valuation, is_model valuation formula ∧
        encodes_tuple csp originals ladder_on valuation tuple := by
  unfold models_over_tuple
  rw [Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨⟨valuation, property⟩, unique⟩
    exact ⟨valuation, property,
      fun other other_property => congrArg Subtype.val (unique ⟨other, other_property⟩)⟩
  · rintro ⟨valuation, property, unique⟩
    exact ⟨⟨valuation, property⟩, fun other => Subtype.ext (unique other.val other.property)⟩

theorem models_over_tuple_eq_one_of_parsimonious {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (formula : cnf_formula (boolean_variable csp ladder_on))
    (projection_exact : is_projection_exact csp originals ladder_on formula)
    (parsimonious : is_parsimonious csp originals formula)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple) :
    models_over_tuple csp originals ladder_on formula tuple = 1 :=
  (models_over_tuple_eq_one_iff csp originals ladder_on formula tuple).mpr
    ((is_parsimonious_iff_unique_models csp originals ladder_on formula projection_exact).mp
      parsimonious tuple in_rel)

theorem linked_composition_parsimonious_of_parsimonious_parts
    (parts : Fin part_count → linked_part domain_size)
    (covers : covers_all_originals (linked_problem parts))
    (exact : ∀ part, is_exact_part (parts part))
    (parts_parsimonious : ∀ part,
      is_parsimonious (parts part).csp (parts part).originals (parts part).formula) :
    model_count (conjunction_formula (linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (linked_problem parts))).card :=
  (linked_composition_parsimonious_iff parts covers exact).mpr fun _ satisfied part =>
    models_over_tuple_eq_one_of_parsimonious _ _ _ _ (exact part).2 (parts_parsimonious part) _
      (satisfied part)

theorem fixes_blocks_of_append (data : linked_part domain_size)
    (rest : cnf_formula (boolean_variable data.csp data.ladder_on))
    (formula_eq : data.formula = exactly_one_part data.csp data.ladder_on ++ rest) :
    fixes_blocks data := by
  intro valuation model
  rw [formula_eq] at model
  exact ((is_model_append valuation _ _).mp model).1

end link

section encodings

variable {vertex_count : ℕ} {domain_size : Fin original_count → ℕ}

def support_part (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)) :
    linked_part domain_size where
  vertex_count := vertex_count
  csp := csp
  originals := originals
  ladder_on := all_vertices
  ladder_covers := fun _ _ => rfl
  embed := embed
  domain_match := domain_match
  formula := support_encoding csp

def direct_part (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)) :
    linked_part domain_size where
  vertex_count := vertex_count
  csp := csp
  originals := originals
  ladder_on := all_vertices
  ladder_covers := fun _ _ => rfl
  embed := embed
  domain_match := domain_match
  formula := direct_encoding csp

def min_eo_part (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count))
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)) :
    linked_part domain_size where
  vertex_count := vertex_count
  csp := csp
  originals := originals
  ladder_on := all_vertices
  ladder_covers := fun _ _ => rfl
  embed := embed
  domain_match := domain_match
  formula := min_eo_encoding csp order

def partial_support_part (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)) :
    linked_part domain_size where
  vertex_count := vertex_count
  csp := csp
  originals := originals
  ladder_on := originals
  ladder_covers := fun _ on_x => on_x
  embed := embed
  domain_match := domain_match
  formula := partial_support_encoding csp originals

def minimal_support_part (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count))
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)) :
    linked_part domain_size where
  vertex_count := vertex_count
  csp := csp
  originals := originals
  ladder_on := originals
  ladder_covers := fun _ on_x => on_x
  embed := embed
  domain_match := domain_match
  formula := minimal_support_encoding csp originals order

theorem support_part_is_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_exact_part (support_part csp originals embed domain_match) :=
  ⟨fixes_blocks_of_append _ (all_support_clauses csp all_vertices) rfl,
    support_is_projection_exact csp originals⟩

theorem direct_part_is_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_exact_part (direct_part csp originals embed domain_match) :=
  ⟨fixes_blocks_of_append _ (all_forbidden_clauses csp all_vertices) rfl,
    direct_is_projection_exact csp originals⟩

theorem min_eo_part_is_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (listed : ∀ x, x ∈ order) (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_exact_part (min_eo_part csp originals order embed domain_match) :=
  ⟨fixes_blocks_of_append _ (tree_order_support_clauses csp all_vertices order) rfl,
    min_eo_listing_is_projection_exact csp order listed originals⟩

theorem partial_support_part_is_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_exact_part (partial_support_part csp originals embed domain_match) :=
  ⟨fixes_blocks_of_append _ (all_support_clauses csp originals) rfl,
    partial_support_is_projection_exact csp originals tree has_original⟩

theorem minimal_support_part_is_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    is_exact_part (minimal_support_part csp originals order embed domain_match) :=
  ⟨fixes_blocks_of_append _ (tree_order_support_clauses csp originals order) rfl,
    minimal_support_is_projection_exact csp originals order tree_order root_original⟩

end encodings

end parsimony
