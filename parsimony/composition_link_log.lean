import parsimony.composition_link_examples

namespace parsimony

variable {original_count part_count : ℕ}

abbrev bit_block (size : ℕ) := Fin (bit_count size)

def bit_block_code (size : ℕ) (value : Fin size) : bit_block size → Bool :=
  fun position => value_bit size value.val position.val

theorem bit_block_code_injective (size : ℕ) : Function.Injective (bit_block_code size) := by
  intro first second same
  exact Fin.ext (eq_of_value_bits_eq size first.val second.val
    (lt_of_lt_of_le first.isLt (le_two_pow_bit_count size))
    (lt_of_lt_of_le second.isLt (le_two_pow_bit_count size))
    (fun position => congrFun same position))

theorem value_bit_of_sizes_equal {first_size second_size : ℕ}
    (sizes_equal : first_size = second_size) (value position : ℕ) :
    value_bit first_size value position = value_bit second_size value position := by
  rw [sizes_equal]

structure log_linked_part (domain_size : Fin original_count → ℕ) where
  vertex_count : ℕ
  csp : binary_csp vertex_count
  originals : Fin vertex_count → Bool
  embed : original_vertex originals → Fin original_count
  domain_match : ∀ x : original_vertex originals, csp.domain_size x.val = domain_size (embed x)

section log_link

variable {domain_size : Fin original_count → ℕ}

abbrev log_part_private_variable (data : log_linked_part domain_size) :=
  {variable_name : log_variable data.csp // data.originals variable_name.1 = false}

abbrev log_linked_part_variable (data : log_linked_part domain_size) :=
  (Σ member : original_vertex data.originals, bit_block (domain_size (data.embed member))) ⊕
    log_part_private_variable data

def to_log_part_variable (data : log_linked_part domain_size) :
    log_variable data.csp → log_linked_part_variable data
  | ⟨x, position⟩ =>
    if on_x : data.originals x = true then
      Sum.inl ⟨⟨x, on_x⟩,
        Fin.cast (congrArg bit_count (data.domain_match ⟨x, on_x⟩)) position⟩
    else Sum.inr ⟨⟨x, position⟩, Bool.eq_false_iff.mpr on_x⟩

def of_log_part_variable (data : log_linked_part domain_size) :
    log_linked_part_variable data → log_variable data.csp
  | Sum.inl ⟨member, position⟩ =>
    ⟨member.val, Fin.cast (congrArg bit_count (data.domain_match member)).symm position⟩
  | Sum.inr hidden_variable => hidden_variable.val

theorem to_log_part_variable_original (data : log_linked_part domain_size)
    (member : original_vertex data.originals)
    (position : Fin (bit_count (data.csp.domain_size member.val))) :
    to_log_part_variable data ⟨member.val, position⟩ =
      Sum.inl ⟨member, Fin.cast (congrArg bit_count (data.domain_match member)) position⟩ := by
  obtain ⟨x, on_x⟩ := member
  simp only [to_log_part_variable]
  split
  · rfl
  · contradiction

theorem to_log_part_variable_private (data : log_linked_part domain_size)
    (variable_name : log_variable data.csp) (hidden : data.originals variable_name.1 = false) :
    to_log_part_variable data variable_name = Sum.inr ⟨variable_name, hidden⟩ := by
  rcases variable_name with ⟨x, position⟩
  change data.originals x = false at hidden
  simp only [to_log_part_variable]
  split
  · rename_i on_x
    exact absurd (hidden.symm.trans on_x) (by decide)
  · rfl

theorem of_to_log_part_variable (data : log_linked_part domain_size)
    (variable_name : log_variable data.csp) :
    of_log_part_variable data (to_log_part_variable data variable_name) = variable_name := by
  by_cases on_owner : data.originals variable_name.1 = true
  · rcases variable_name with ⟨x, position⟩
    change data.originals x = true at on_owner
    rw [to_log_part_variable_original data ⟨x, on_owner⟩ position]
    rfl
  · rw [to_log_part_variable_private data variable_name (Bool.eq_false_iff.mpr on_owner)]
    rfl

theorem to_of_log_part_variable (data : log_linked_part domain_size)
    (part_variable_name : log_linked_part_variable data) :
    to_log_part_variable data (of_log_part_variable data part_variable_name) =
      part_variable_name := by
  rcases part_variable_name with ⟨member, position⟩ | ⟨variable_name, hidden⟩
  · show to_log_part_variable data
      ⟨member.val, Fin.cast (congrArg bit_count (data.domain_match member)).symm position⟩ = _
    rw [to_log_part_variable_original]
    rfl
  · exact to_log_part_variable_private data variable_name hidden

def log_valuation_equiv (data : log_linked_part domain_size) :
    (log_linked_part_variable data → Bool) ≃ (log_variable data.csp → Bool) where
  toFun := fun valuation => valuation ∘ to_log_part_variable data
  invFun := fun concrete => concrete ∘ of_log_part_variable data
  left_inv := fun valuation => by
    funext part_variable_name
    exact congrArg valuation (to_of_log_part_variable data part_variable_name)
  right_inv := fun concrete => by
    funext variable_name
    exact congrArg concrete (of_to_log_part_variable data variable_name)

def log_concrete_tuple (data : log_linked_part domain_size)
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    original_tuple data.csp data.originals :=
  fun member => Fin.cast (data.domain_match member).symm (tuple member)

def log_abstract_tuple (data : log_linked_part domain_size)
    (tuple : original_tuple data.csp data.originals) :
    ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member)) :=
  fun member => Fin.cast (data.domain_match member) (tuple member)

theorem log_concrete_abstract_tuple (data : log_linked_part domain_size)
    (tuple : original_tuple data.csp data.originals) :
    log_concrete_tuple data (log_abstract_tuple data tuple) = tuple := by
  funext member
  exact Fin.ext rfl

def log_tuple_on_part (data : log_linked_part domain_size)
    (tuple : ∀ original, Fin (domain_size original)) : original_tuple data.csp data.originals :=
  fun member => Fin.cast (data.domain_match member).symm (tuple (data.embed member))

def log_linked_encodes (data : log_linked_part domain_size)
    (valuation : log_linked_part_variable data → Bool)
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    Prop :=
  ∀ member position, valuation (Sum.inl ⟨member, position⟩) =
    bit_block_code (domain_size (data.embed member)) (tuple member) position

theorem log_linked_encodes_iff (data : log_linked_part domain_size)
    (valuation : log_linked_part_variable data → Bool)
    (tuple : ∀ member : original_vertex data.originals, Fin (domain_size (data.embed member))) :
    log_linked_encodes data valuation tuple ↔
      log_encodes_tuple data.csp data.originals (valuation ∘ to_log_part_variable data)
        (log_concrete_tuple data tuple) := by
  constructor
  · intro encodes member position
    show valuation (to_log_part_variable data ⟨member.val, position⟩) =
      value_bit (data.csp.domain_size member.val) (log_concrete_tuple data tuple member).val
        position.val
    rw [to_log_part_variable_original,
      encodes member (Fin.cast (congrArg bit_count (data.domain_match member)) position)]
    exact (value_bit_of_sizes_equal (data.domain_match member) (tuple member).val position.val).symm
  · intro encodes member block_position
    obtain ⟨position, rfl⟩ : ∃ position,
        Fin.cast (congrArg bit_count (data.domain_match member)) position = block_position :=
      ⟨Fin.cast (congrArg bit_count (data.domain_match member)).symm block_position,
        Fin.ext rfl⟩
    rw [← to_log_part_variable_original data member position]
    refine (encodes member position).trans ?_
    exact value_bit_of_sizes_equal (data.domain_match member) (tuple member).val position.val

def log_linked_problem (parts : Fin part_count → log_linked_part domain_size) :
    composition_problem original_count part_count where
  domain_size := domain_size
  block_type := fun original => bit_block (domain_size original)
  block_fintype := fun _ => inferInstance
  block_decidable_eq := fun _ => inferInstance
  block_code := fun original => bit_block_code (domain_size original)
  block_code_injective := fun original => bit_block_code_injective (domain_size original)
  scope_type := fun part => original_vertex (parts part).originals
  scope_fintype := fun _ => inferInstance
  scope_decidable_eq := fun _ => inferInstance
  scope_original := fun part => (parts part).embed
  private_type := fun part => log_part_private_variable (parts part)
  private_fintype := fun _ => inferInstance
  private_decidable_eq := fun _ => inferInstance
  part_formula := fun part =>
    rename_formula (to_log_part_variable (parts part)) (log_encoding (parts part).csp)
  part_relation := fun part tuple =>
    in_relation (parts part).csp (parts part).originals (log_concrete_tuple (parts part) tuple)
  part_relation_decidable := fun _ _ => inferInstance

theorem log_linked_part_formula_model_iff (parts : Fin part_count → log_linked_part domain_size)
    (part : Fin part_count) (valuation : part_variable (log_linked_problem parts) part → Bool) :
    is_model valuation ((log_linked_problem parts).part_formula part) ↔
      is_model (valuation ∘ to_log_part_variable (parts part)) (log_encoding (parts part).csp) :=
  is_model_rename_formula_iff _ _ _

theorem log_linked_part_encodes_iff (parts : Fin part_count → log_linked_part domain_size)
    (part : Fin part_count) (valuation : part_variable (log_linked_problem parts) part → Bool)
    (tuple : part_tuple (log_linked_problem parts) part) :
    part_encodes (log_linked_problem parts) part valuation tuple ↔
      log_linked_encodes (parts part) valuation tuple :=
  Iff.rfl

theorem log_linked_part_relation_iff (parts : Fin part_count → log_linked_part domain_size)
    (part : Fin part_count) (tuple : part_tuple (log_linked_problem parts) part) :
    (log_linked_problem parts).part_relation part tuple ↔
      in_relation (parts part).csp (parts part).originals
        (log_concrete_tuple (parts part) tuple) :=
  Iff.rfl

theorem log_linked_satisfies_all_parts_iff (parts : Fin part_count → log_linked_part domain_size)
    (tuple : global_tuple (log_linked_problem parts)) :
    satisfies_all_parts (log_linked_problem parts) tuple ↔
      ∀ part, in_relation (parts part).csp (parts part).originals
        (log_tuple_on_part (parts part) tuple) :=
  Iff.rfl

theorem log_linked_covers_iff (parts : Fin part_count → log_linked_part domain_size) :
    covers_all_originals (log_linked_problem parts) ↔
      ∀ original, ∃ part, ∃ member : original_vertex (parts part).originals,
        (parts part).embed member = original :=
  Iff.rfl

theorem log_linked_global_encodes_iff (parts : Fin part_count → log_linked_part domain_size)
    (valuation : global_variable (log_linked_problem parts) → Bool)
    (tuple : ∀ original, Fin (domain_size original)) :
    global_encodes (log_linked_problem parts) valuation tuple ↔
      ∀ (original : Fin original_count) (position : Fin (bit_count (domain_size original))),
        valuation (Sum.inl ⟨original, position⟩) =
          value_bit (domain_size original) (tuple original).val position.val :=
  Iff.rfl

theorem log_linked_part_models_over (parts : Fin part_count → log_linked_part domain_size)
    (part : Fin part_count) (tuple : part_tuple (log_linked_problem parts) part) :
    part_models_over (log_linked_problem parts) part tuple =
      log_models_over_tuple (parts part).csp (parts part).originals
        (log_concrete_tuple (parts part) tuple) := by
  unfold part_models_over log_models_over_tuple
  refine Fintype.card_congr (Equiv.subtypeEquiv (log_valuation_equiv (parts part)) ?_)
  intro valuation
  exact and_congr (log_linked_part_formula_model_iff parts part valuation)
    (log_linked_encodes_iff (parts part) valuation tuple)

theorem log_linked_part_is_projection_exact (parts : Fin part_count → log_linked_part domain_size)
    (part : Fin part_count) : part_is_projection_exact (log_linked_problem parts) part := by
  have projection_exact :=
    log_is_projection_exact_theorem (parts part).csp (parts part).originals
  constructor
  · intro valuation model
    have concrete_model := (log_linked_part_formula_model_iff parts part valuation).mp model
    obtain ⟨tuple, in_rel, encodes⟩ := projection_exact.1 _ concrete_model
    refine ⟨log_abstract_tuple (parts part) tuple, ?_, ?_⟩
    · show in_relation (parts part).csp (parts part).originals
        (log_concrete_tuple (parts part) (log_abstract_tuple (parts part) tuple))
      rw [log_concrete_abstract_tuple]
      exact in_rel
    · refine (log_linked_encodes_iff (parts part) valuation _).mpr ?_
      rw [log_concrete_abstract_tuple]
      exact encodes
  · intro tuple in_rel
    have concrete_in_rel : in_relation (parts part).csp (parts part).originals
        (log_concrete_tuple (parts part) tuple) := in_rel
    obtain ⟨concrete, concrete_model, encodes⟩ := projection_exact.2 _ concrete_in_rel
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
      exact encodes
    exact ⟨concrete ∘ of_log_part_variable (parts part),
      (log_linked_part_formula_model_iff parts part _).mpr lifted_model,
      (log_linked_encodes_iff (parts part) _ tuple).mpr lifted_encodes⟩

theorem log_composition_model_count (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts)) :
    model_count (conjunction_formula (log_linked_problem parts)) =
      ∑ tuple ∈ Finset.univ.filter (satisfies_all_parts (log_linked_problem parts)),
        ∏ part, log_models_over_tuple (parts part).csp (parts part).originals
          (log_tuple_on_part (parts part) tuple) := by
  rw [composition_model_count (log_linked_problem parts) covers
    (fun part => log_linked_part_is_projection_exact parts part)]
  refine Finset.sum_congr rfl fun tuple _ => Finset.prod_congr rfl fun part _ => ?_
  exact log_linked_part_models_over parts part _

theorem log_composition_model_count_by_extensions
    (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts)) :
    model_count (conjunction_formula (log_linked_problem parts)) =
      ∑ tuple ∈ Finset.univ.filter (satisfies_all_parts (log_linked_problem parts)),
        ∏ part, extension_count (parts part).csp (parts part).originals
          (log_tuple_on_part (parts part) tuple) := by
  rw [log_composition_model_count parts covers]
  refine Finset.sum_congr rfl fun tuple _ => Finset.prod_congr rfl fun part _ => ?_
  exact log_models_over_tuple_eq_extension_count _ _ _

theorem log_composition_factor_positive (parts : Fin part_count → log_linked_part domain_size)
    (tuple : global_tuple (log_linked_problem parts))
    (satisfied : satisfies_all_parts (log_linked_problem parts) tuple) (part : Fin part_count) :
    0 < log_models_over_tuple (parts part).csp (parts part).originals
      (log_tuple_on_part (parts part) tuple) := by
  have positive := composition_factor_positive (log_linked_problem parts)
    (fun part => log_linked_part_is_projection_exact parts part) tuple satisfied part
  rw [log_linked_part_models_over parts part] at positive
  exact positive

theorem log_composition_projection_exact (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts)) :
    (∀ valuation, is_model valuation (conjunction_formula (log_linked_problem parts)) →
      ∃ tuple, satisfies_all_parts (log_linked_problem parts) tuple ∧
        global_encodes (log_linked_problem parts) valuation tuple) ∧
    (∀ tuple, satisfies_all_parts (log_linked_problem parts) tuple →
      ∃ valuation, is_model valuation (conjunction_formula (log_linked_problem parts)) ∧
        global_encodes (log_linked_problem parts) valuation tuple) :=
  composition_projection_exact (log_linked_problem parts) covers
    (fun part => log_linked_part_is_projection_exact parts part)

theorem log_composition_parsimonious_iff (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts)) :
    model_count (conjunction_formula (log_linked_problem parts)) =
        (Finset.univ.filter (satisfies_all_parts (log_linked_problem parts))).card ↔
      ∀ tuple, satisfies_all_parts (log_linked_problem parts) tuple →
        ∀ part, log_models_over_tuple (parts part).csp (parts part).originals
          (log_tuple_on_part (parts part) tuple) = 1 := by
  rw [composition_parsimonious_iff (log_linked_problem parts) covers
    (fun part => log_linked_part_is_projection_exact parts part)]
  refine forall_congr' fun tuple => imp_congr_right fun _ => forall_congr' fun part => ?_
  have same := log_linked_part_models_over parts part
    (restrict_to_part (log_linked_problem parts) tuple part)
  constructor
  · intro count_one
    exact same.symm.trans count_one
  · intro count_one
    exact same.trans count_one

theorem log_composition_parsimonious_iff_one_extension
    (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts)) :
    model_count (conjunction_formula (log_linked_problem parts)) =
        (Finset.univ.filter (satisfies_all_parts (log_linked_problem parts))).card ↔
      ∀ tuple, satisfies_all_parts (log_linked_problem parts) tuple →
        ∀ part, extension_count (parts part).csp (parts part).originals
          (log_tuple_on_part (parts part) tuple) = 1 := by
  rw [log_composition_parsimonious_iff parts covers]
  refine forall_congr' fun tuple => imp_congr_right fun _ => forall_congr' fun part => ?_
  rw [log_models_over_tuple_eq_extension_count]

theorem log_composition_parsimonious_of_parsimonious_parts
    (parts : Fin part_count → log_linked_part domain_size)
    (covers : covers_all_originals (log_linked_problem parts))
    (parts_parsimonious : ∀ part,
      is_parsimonious (parts part).csp (parts part).originals (log_encoding (parts part).csp)) :
    model_count (conjunction_formula (log_linked_problem parts)) =
      (Finset.univ.filter (satisfies_all_parts (log_linked_problem parts))).card :=
  (log_composition_parsimonious_iff_one_extension parts covers).mpr fun _ satisfied part =>
    (log_parsimonious_iff (parts part).csp (parts part).originals).mp (parts_parsimonious part) _
      (satisfied part)

end log_link

section log_encoding_part

variable {vertex_count : ℕ} {domain_size : Fin original_count → ℕ}

def log_part (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (embed : original_vertex originals → Fin original_count)
    (domain_match : ∀ x : original_vertex originals,
      csp.domain_size x.val = domain_size (embed x)) :
    log_linked_part domain_size where
  vertex_count := vertex_count
  csp := csp
  originals := originals
  embed := embed
  domain_match := domain_match

end log_encoding_part

namespace counterexamples

def conjunction_log_parts : Fin 2 → log_linked_part conjunction_sizes :=
  ![log_part conjunction_part_csp first_vertex_is_original conjunction_embed conjunction_domain_match,
    log_part conjunction_restriction_csp all_vertices identity_embed conjunction_restriction_domain_match]

theorem conjunction_log_composition_covers :
    covers_all_originals (log_linked_problem conjunction_log_parts) := by
  unfold covers_all_originals
  decide +kernel

theorem conjunction_log_composition :
    (Finset.univ.filter (satisfies_all_parts (log_linked_problem conjunction_log_parts))).card = 1 ∧
      model_count (conjunction_formula (log_linked_problem conjunction_log_parts)) = 1 := by
  decide +kernel

theorem conjunction_log_part_is_not_parsimonious :
    ¬ is_parsimonious conjunction_part_csp first_vertex_is_original
      (log_encoding conjunction_part_csp) := by
  rw [log_parsimonious_iff]
  decide +kernel

end counterexamples

end parsimony
