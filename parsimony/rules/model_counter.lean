import parsimony.extended_definitions

namespace parsimony
namespace rules

def clause_ok (truth : ℕ) (clause : cnf_clause ℕ) : Bool :=
  clause.any fun literal => truth.testBit literal.1 == literal.2

def level_count : List (cnf_formula ℕ) → ℕ → ℕ → ℕ
  | [], _, _ => 1
  | clauses :: rest, position, truth =>
    (if clauses.all (clause_ok truth) then level_count rest (position + 1) truth else 0) +
      if clauses.all (clause_ok (truth + 2 ^ position)) then
        level_count rest (position + 1) (truth + 2 ^ position) else 0

def levels_bounded : List (cnf_formula ℕ) → ℕ → Bool
  | [], _ => true
  | clauses :: rest, position =>
    (clauses.all fun clause => clause.all fun literal => decide (literal.1 ≤ position)) &&
      levels_bounded rest (position + 1)

theorem clause_ok_iff (truth : ℕ) (clause : cnf_clause ℕ) :
    clause_ok truth clause = true ↔ ∃ literal ∈ clause, truth.testBit literal.1 = literal.2 := by
  simp [clause_ok, List.any_eq_true, beq_iff_eq]

theorem clause_ok_mod (whole position : ℕ) (clause : cnf_clause ℕ)
    (bounded : ∀ literal ∈ clause, literal.1 ≤ position) :
    clause_ok (whole % 2 ^ (position + 1)) clause = clause_ok whole clause := by
  rw [Bool.eq_iff_iff, clause_ok_iff, clause_ok_iff]
  refine exists_congr fun literal => and_congr_right fun literal_mem => ?_
  rw [Nat.testBit_mod_two_pow]
  have small : literal.1 < position + 1 := Nat.lt_succ_of_le (bounded literal literal_mem)
  simp [small]

theorem mod_split (whole position truth : ℕ) (truth_lt : truth < 2 ^ position) :
    whole % 2 ^ position = truth ↔
      whole % 2 ^ (position + 1) = truth ∨ whole % 2 ^ (position + 1) = truth + 2 ^ position := by
  have positive : 0 < 2 ^ position := Nat.two_pow_pos position
  have double : 2 ^ (position + 1) = 2 ^ position * 2 := pow_succ 2 position
  rw [double, Nat.mod_mul]
  have bit : whole / 2 ^ position % 2 = 0 ∨ whole / 2 ^ position % 2 = 1 := by omega
  rcases bit with zero | one
  · rw [zero]
    constructor
    · intro same
      exact Or.inl (by simpa using same)
    · rintro (same | same)
      · simpa using same
      · have small : whole % 2 ^ position < 2 ^ position := Nat.mod_lt _ positive
        omega
  · rw [one]
    constructor
    · intro same
      exact Or.inr (by omega)
    · rintro (same | same)
      · omega
      · omega

theorem level_count_eq (levels : List (cnf_formula ℕ)) (position truth : ℕ)
    (truth_lt : truth < 2 ^ position) (bounded : levels_bounded levels position = true) :
    level_count levels position truth =
      ((Finset.range (2 ^ (position + levels.length))).filter fun whole =>
        whole % 2 ^ position = truth ∧
          ∀ clauses ∈ levels, ∀ clause ∈ clauses, clause_ok whole clause = true).card := by
  induction levels generalizing position truth with
  | nil =>
    have only : (Finset.range (2 ^ (position + ([] : List (cnf_formula ℕ)).length))).filter (fun whole =>
        whole % 2 ^ position = truth ∧
          ∀ clauses ∈ ([] : List (cnf_formula ℕ)), ∀ clause ∈ clauses, clause_ok whole clause = true) =
        {truth} := by
      ext whole
      simp only [List.length_nil, Nat.add_zero, Finset.mem_filter, Finset.mem_range, List.not_mem_nil,
        false_imp_iff, implies_true, and_true, Finset.mem_singleton]
      constructor
      · rintro ⟨small, same⟩
        rwa [Nat.mod_eq_of_lt small] at same
      · rintro rfl
        exact ⟨truth_lt, Nat.mod_eq_of_lt truth_lt⟩
    rw [only]
    rfl
  | cons clauses rest hypothesis =>
    simp only [levels_bounded, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at bounded
    obtain ⟨first_bounded, rest_bounded⟩ := bounded
    have length_is : position + (clauses :: rest).length = position + 1 + rest.length := by
      simp only [List.length_cons]
      omega
    have double : 2 ^ (position + 1) = 2 ^ position * 2 := pow_succ 2 position
    have low_lt : truth < 2 ^ (position + 1) := by omega
    have high_lt : truth + 2 ^ position < 2 ^ (position + 1) := by omega
    have part : ∀ low, low < 2 ^ (position + 1) →
        (if clauses.all (clause_ok low) then level_count rest (position + 1) low else 0) =
          ((Finset.range (2 ^ (position + 1 + rest.length))).filter fun whole =>
            whole % 2 ^ (position + 1) = low ∧
              ∀ other ∈ clauses :: rest, ∀ clause ∈ other, clause_ok whole clause = true).card := by
      intro low low_small
      have first_level : ∀ whole, whole % 2 ^ (position + 1) = low →
          ((∀ clause ∈ clauses, clause_ok whole clause = true) ↔ clauses.all (clause_ok low) = true) := by
        intro whole same
        rw [List.all_eq_true]
        refine forall_congr' fun clause => imp_congr_right fun clause_mem => ?_
        rw [← same, clause_ok_mod whole position clause (first_bounded clause clause_mem)]
      by_cases ok : clauses.all (clause_ok low) = true
      · rw [ite_eq_left ok, hypothesis (position + 1) low low_small rest_bounded]
        congr 1
        refine Finset.filter_congr fun whole _ => and_congr_right fun same => ?_
        rw [List.forall_mem_cons]
        exact ⟨fun rest_ok => ⟨(first_level whole same).mpr ok, rest_ok⟩, fun both => both.2⟩
      · rw [ite_eq_right ok]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro whole _ ⟨same, all_ok⟩
        exact ok ((first_level whole same).mp (all_ok clauses (List.mem_cons_self ..)))
    rw [level_count, part truth low_lt, part (truth + 2 ^ position) high_lt, length_is,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext whole
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      rw [mod_split whole position truth truth_lt]
      tauto
    · rw [Finset.disjoint_filter]
      rintro whole _ ⟨first_same, _⟩ ⟨second_same, _⟩
      have positive : 0 < 2 ^ position := Nat.two_pow_pos position
      omega

def rename_by {boolean_type : Type} [DecidableEq boolean_type] (variable_list : List boolean_type)
    (formula : cnf_formula boolean_type) : cnf_formula ℕ :=
  formula.map fun clause => clause.map fun literal => (variable_list.idxOf literal.1, literal.2)

def same_clauses (first second : cnf_formula ℕ) : Bool :=
  (first.all fun clause => second.contains clause) && second.all fun clause => first.contains clause

theorem same_clauses_iff (first second : cnf_formula ℕ) (same : same_clauses first second = true) :
    ∀ clause, clause ∈ first ↔ clause ∈ second := by
  simp only [same_clauses, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at same
  exact fun clause => ⟨same.1 clause, same.2 clause⟩

theorem model_count_eq_level_count {boolean_type : Type} [Fintype boolean_type]
    [DecidableEq boolean_type] (formula : cnf_formula boolean_type) (variable_list : List boolean_type)
    (nodup : variable_list.Nodup) (complete : ∀ variable_name, variable_name ∈ variable_list)
    (levels : List (cnf_formula ℕ)) (length_ok : levels.length = variable_list.length)
    (bounded : levels_bounded levels 0 = true)
    (same : same_clauses levels.flatten (rename_by variable_list formula) = true) :
    model_count formula = level_count levels 0 0 := by
  rw [level_count_eq levels 0 0 (by simp) bounded]
  unfold model_count
  rw [Fintype.card_subtype]
  have index_lt : ∀ variable_name, variable_list.idxOf variable_name < variable_list.length :=
    fun variable_name => List.idxOf_lt_length_of_mem (complete variable_name)
  have holds_iff : ∀ whole, (∀ clauses ∈ levels, ∀ clause ∈ clauses, clause_ok whole clause = true) ↔
      is_model (fun variable_name => whole.testBit (variable_list.idxOf variable_name)) formula := by
    intro whole
    have flat : (∀ clauses ∈ levels, ∀ clause ∈ clauses, clause_ok whole clause = true) ↔
        ∀ clause ∈ levels.flatten, clause_ok whole clause = true := by
      simp only [List.mem_flatten]
      constructor
      · rintro all_ok clause ⟨clauses, clauses_mem, clause_mem⟩
        exact all_ok clauses clauses_mem clause clause_mem
      · intro all_ok clauses clauses_mem clause clause_mem
        exact all_ok clause ⟨clauses, clauses_mem, clause_mem⟩
    rw [flat]
    have renamed : (∀ clause ∈ levels.flatten, clause_ok whole clause = true) ↔
        ∀ clause ∈ rename_by variable_list formula, clause_ok whole clause = true :=
      forall_congr' fun clause => imp_congr_left (same_clauses_iff _ _ same clause)
    rw [renamed]
    simp only [rename_by, List.forall_mem_map]
    refine forall_congr' fun clause => imp_congr_right fun _ => ?_
    rw [clause_ok_iff]
    unfold clause_holds
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨literal, literal_mem, rfl⟩, holds⟩
      exact ⟨literal, literal_mem, holds⟩
    · rintro ⟨literal, literal_mem, holds⟩
      exact ⟨_, ⟨literal, literal_mem, rfl⟩, holds⟩
  symm
  refine Finset.card_bij
    (fun whole _ => fun variable_name => whole.testBit (variable_list.idxOf variable_name)) ?_ ?_ ?_
  · intro whole whole_mem
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at whole_mem ⊢
    exact (holds_iff whole).mp whole_mem.2.2
  · intro first first_mem second second_mem same_function
    simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add, length_ok] at first_mem second_mem
    refine Nat.eq_of_testBit_eq fun position => ?_
    by_cases inside : position < variable_list.length
    · have at_position := congrFun same_function (variable_list.get ⟨position, inside⟩)
      have index_is : variable_list.idxOf (variable_list.get ⟨position, inside⟩) = position :=
        nodup.idxOf_getElem position inside
      rwa [index_is] at at_position
    · have power_le : 2 ^ variable_list.length ≤ 2 ^ position :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (first_mem.1.trans_le power_le),
        Nat.testBit_lt_two_pow (second_mem.1.trans_le power_le)]
  · intro valuation valuation_mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at valuation_mem
    let whole := Nat.ofBits fun position : Fin variable_list.length => valuation (variable_list.get position)
    have back : (fun variable_name => whole.testBit (variable_list.idxOf variable_name)) = valuation := by
      funext variable_name
      have bit := Nat.testBit_ofBits_lt
        (fun position : Fin variable_list.length => valuation (variable_list.get position))
        (variable_list.idxOf variable_name) (index_lt variable_name)
      refine bit.trans ?_
      congr 1
      exact List.getElem_idxOf (index_lt variable_name)
    refine ⟨whole, ?_, back⟩
    simp only [Finset.mem_filter, Finset.mem_range, Nat.zero_add, length_ok, pow_zero, Nat.mod_one,
      true_and]
    refine ⟨Nat.ofBits_lt_two_pow _, (holds_iff whole).mpr ?_⟩
    rw [back]
    exact valuation_mem

def variables_in_order {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (order : List (Fin vertex_count)) :
    List (boolean_variable csp ladder_on) :=
  order.flatMap fun x =>
    ((List.finRange (csp.domain_size x)).map fun a => Sum.inl ⟨x, a⟩) ++
      if on_x : ladder_on x = true then
        (List.finRange (csp.domain_size x - 1)).map fun position => Sum.inr ⟨⟨x, on_x⟩, position⟩
      else []

end rules
end parsimony
