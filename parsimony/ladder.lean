import parsimony.definitions

namespace parsimony

theorem exists_threshold (limit : ℕ) (sequence : ℕ → Bool) (at_zero : sequence 0 = true)
    (at_limit : sequence limit = false)
    (descends : ∀ i, sequence (i + 1) = true → sequence i = true) :
    ∃ threshold, threshold < limit ∧ ∀ i, sequence i = decide (i ≤ threshold) := by
  classical
  have has_false : ∃ m, sequence m = false := ⟨limit, at_limit⟩
  have first_false := Nat.find_spec has_false
  have first_false_le : Nat.find has_false ≤ limit := Nat.find_min' has_false at_limit
  have first_false_positive : 0 < Nat.find has_false := by
    rcases Nat.eq_zero_or_pos (Nat.find has_false) with is_zero | is_positive
    · rw [is_zero, at_zero] at first_false
      exact absurd first_false (by decide)
    · exact is_positive
  have stays_false : ∀ gap, sequence (Nat.find has_false + gap) = false := by
    intro gap
    induction gap with
    | zero => simpa using first_false
    | succ gap previous =>
      by_contra not_false
      have is_true : sequence (Nat.find has_false + gap + 1) = true := by
        simpa [Nat.add_assoc] using not_false
      rw [descends _ is_true] at previous
      exact absurd previous (by decide)
  refine ⟨Nat.find has_false - 1, by omega, ?_⟩
  intro i
  by_cases early : i ≤ Nat.find has_false - 1
  · have before_first : i < Nat.find has_false := by omega
    have not_false := Nat.find_min has_false before_first
    simpa [early] using not_false
  · have gap_form : i = Nat.find has_false + (i - Nat.find has_false) := by omega
    rw [decide_eq_false early, gap_form]
    exact stays_false _

def ladder_sequence {count : ℕ} (ladder_val : Fin count → Bool) : ℕ → Bool
  | 0 => true
  | j + 1 => if bound : j < count then ladder_val ⟨j, bound⟩ else false

theorem ladder_sequence_zero {count : ℕ} (ladder_val : Fin count → Bool) :
    ladder_sequence ladder_val 0 = true := rfl

theorem ladder_sequence_succ {count : ℕ} (ladder_val : Fin count → Bool) (j : ℕ)
    (bound : j < count) : ladder_sequence ladder_val (j + 1) = ladder_val ⟨j, bound⟩ := by
  simp [ladder_sequence, bound]

theorem ladder_sequence_beyond {count : ℕ} (ladder_val : Fin count → Bool) (j : ℕ)
    (beyond : ¬ j < count) : ladder_sequence ladder_val (j + 1) = false := by
  simp [ladder_sequence, beyond]

theorem exactly_one_unit_hold_iff {literal_type : Type}
    (value_lit : Fin 1 → Bool → literal_type) (ladder_lit : Fin (1 - 1) → Bool → literal_type)
    (literal_holds : literal_type → Prop)
    (value_val : Fin 1 → Bool) (ladder_val : Fin (1 - 1) → Bool)
    (value_holds : ∀ a polarity, literal_holds (value_lit a polarity) ↔ value_val a = polarity) :
    (∀ clause ∈ exactly_one_clauses 1 value_lit ladder_lit,
        ∃ literal ∈ clause, literal_holds literal) ↔
      ∃ chosen : Fin 1,
        (∀ a, value_val a = decide (a = chosen)) ∧
          ∀ i, ladder_val i = decide (i.val < chosen.val) := by
  constructor
  · intro clauses_hold
    have unit_clause := clauses_hold [value_lit ⟨0, by omega⟩ true]
      (by simp [exactly_one_clauses])
    simp only [List.mem_singleton, exists_eq_left, value_holds] at unit_clause
    refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · intro a
      have a_is_zero : a = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [a_is_zero, unit_clause]
      simp
    · intro i
      exact absurd i.isLt (by omega)
  · rintro ⟨chosen, value_eq, _⟩ clause clause_member
    simp only [exactly_one_clauses, List.mem_singleton] at clause_member
    subst clause_member
    simp only [List.mem_singleton, exists_eq_left, value_holds, value_eq]
    have chosen_is_zero : (⟨0, by omega⟩ : Fin 1) = chosen := Fin.ext (by omega)
    simp [chosen_is_zero]

theorem exactly_one_ladder_hold_iff (size : ℕ) {literal_type : Type}
    (value_lit : Fin (size + 2) → Bool → literal_type)
    (ladder_lit : Fin (size + 2 - 1) → Bool → literal_type)
    (literal_holds : literal_type → Prop)
    (value_val : Fin (size + 2) → Bool) (ladder_val : Fin (size + 2 - 1) → Bool)
    (value_holds : ∀ a polarity, literal_holds (value_lit a polarity) ↔ value_val a = polarity)
    (ladder_holds : ∀ i polarity, literal_holds (ladder_lit i polarity) ↔ ladder_val i = polarity) :
    (∀ clause ∈ exactly_one_clauses (size + 2) value_lit ladder_lit,
        ∃ literal ∈ clause, literal_holds literal) ↔
      ∃ chosen : Fin (size + 2),
        (∀ a, value_val a = decide (a = chosen)) ∧
          ∀ i, ladder_val i = decide (i.val < chosen.val) := by
  constructor
  · intro clauses_hold
    have first_negative := clauses_hold
      [value_lit ⟨0, by omega⟩ false, ladder_lit ⟨0, by omega⟩ false]
      (by simp [exactly_one_clauses])
    have first_positive := clauses_hold
      [value_lit ⟨0, by omega⟩ true, ladder_lit ⟨0, by omega⟩ true]
      (by simp [exactly_one_clauses])
    have last_positive := clauses_hold
      [value_lit ⟨size + 1, by omega⟩ true, ladder_lit ⟨size, by omega⟩ false]
      (by simp [exactly_one_clauses])
    have last_negative := clauses_hold
      [value_lit ⟨size + 1, by omega⟩ false, ladder_lit ⟨size, by omega⟩ true]
      (by simp [exactly_one_clauses])
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      value_holds, ladder_holds] at first_negative first_positive last_positive last_negative
    have middle_clauses : ∀ middle : Fin size, ∀ clause ∈
        [[ladder_lit ⟨middle.val, by have := middle.isLt; omega⟩ true,
            ladder_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false],
          [value_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ true,
            ladder_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ true,
            ladder_lit ⟨middle.val, by have := middle.isLt; omega⟩ false],
          [value_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false,
            ladder_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false],
          [value_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false,
            ladder_lit ⟨middle.val, by have := middle.isLt; omega⟩ true]],
        ∃ literal ∈ clause, literal_holds literal := by
      intro middle clause clause_member
      apply clauses_hold
      unfold exactly_one_clauses
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨middle, List.mem_finRange middle, clause_member⟩)
    have sequence_succ : ∀ j (bound : j < size + 2 - 1),
        ladder_sequence ladder_val (j + 1) = ladder_val ⟨j, bound⟩ :=
      fun j bound => ladder_sequence_succ ladder_val j bound
    have sequence_limit : ladder_sequence ladder_val (size + 2) = false :=
      ladder_sequence_beyond ladder_val (size + 1) (by omega)
    have sequence_descends : ∀ i, ladder_sequence ladder_val (i + 1) = true →
        ladder_sequence ladder_val i = true := by
      intro i later_true
      rcases i with _ | j
      · rfl
      · by_cases inner : j + 1 < size + 2 - 1
        · have middle_bound : j < size := by omega
          have clause := middle_clauses ⟨j, middle_bound⟩ _ (List.mem_cons_self)
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
            ladder_holds] at clause
          rw [sequence_succ j (by omega)]
          rw [sequence_succ (j + 1) inner] at later_true
          rcases clause with is_true | is_false
          · exact is_true
          · rw [later_true] at is_false
            exact absurd is_false (by decide)
        · rw [ladder_sequence_beyond ladder_val (j + 1) inner] at later_true
          exact absurd later_true (by decide)
    obtain ⟨threshold, threshold_bound, sequence_eq⟩ :=
      exists_threshold (size + 2) (ladder_sequence ladder_val) rfl sequence_limit sequence_descends
    have value_formula : ∀ a : Fin (size + 2),
        value_val a =
          (ladder_sequence ladder_val a.val && !ladder_sequence ladder_val (a.val + 1)) := by
      rintro ⟨a, a_bound⟩
      by_cases a_first : a = 0
      · subst a_first
        rw [sequence_succ 0 (by omega)]
        simp only [ladder_sequence_zero]
        cases value_case : value_val ⟨0, by omega⟩ <;>
          cases ladder_case : ladder_val ⟨0, by omega⟩ <;>
          simp_all
      · by_cases a_last : a = size + 1
        · subst a_last
          rw [sequence_succ size (by omega)]
          have after_last : ladder_sequence ladder_val (size + 1 + 1) = false := sequence_limit
          simp only [after_last]
          cases value_case : value_val ⟨size + 1, by omega⟩ <;>
            cases ladder_case : ladder_val ⟨size, by omega⟩ <;>
            simp_all
        · obtain ⟨j, rfl⟩ : ∃ j, a = j + 1 := ⟨a - 1, by omega⟩
          have middle_bound : j < size := by omega
          have clause_two := middle_clauses ⟨j, middle_bound⟩ _
            (List.mem_cons_of_mem _ List.mem_cons_self)
          have clause_three := middle_clauses ⟨j, middle_bound⟩ _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          have clause_four := middle_clauses ⟨j, middle_bound⟩ _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              List.mem_cons_self)))
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
            value_holds, ladder_holds] at clause_two clause_three clause_four
          rw [sequence_succ j (by omega), sequence_succ (j + 1) (by omega)]
          cases value_case : value_val ⟨j + 1, by omega⟩ <;>
            cases ladder_low : ladder_val ⟨j, by omega⟩ <;>
            cases ladder_high : ladder_val ⟨j + 1, by omega⟩ <;>
            simp_all
    refine ⟨⟨threshold, threshold_bound⟩, ?_, ?_⟩
    · intro a
      rw [value_formula a, sequence_eq a.val, sequence_eq (a.val + 1)]
      by_cases a_equals : a.val = threshold
      · have same : a = ⟨threshold, threshold_bound⟩ := Fin.ext a_equals
        simp [same]
      · have different : a ≠ ⟨threshold, threshold_bound⟩ := fun same =>
          a_equals (congrArg Fin.val same)
        rw [decide_eq_false different]
        by_cases a_below : a.val ≤ threshold
        · have next_below : a.val + 1 ≤ threshold := by omega
          simp [next_below]
        · simp [a_below]
    · intro i
      rw [← sequence_succ i.val i.isLt, sequence_eq (i.val + 1)]
      by_cases below : i.val < threshold
      · have next_below : i.val + 1 ≤ threshold := by omega
        simp [below, next_below]
      · have next_above : ¬ i.val + 1 ≤ threshold := by omega
        simp [below, next_above]
  · rintro ⟨chosen, value_eq, ladder_eq⟩ clause clause_member
    have chosen_bound := chosen.isLt
    unfold exactly_one_clauses at clause_member
    rcases List.mem_append.mp clause_member with fixed_part | middle_part
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed_part
      rcases fixed_part with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
          value_holds, ladder_holds, value_eq, ladder_eq, decide_eq_true_eq, decide_eq_false_iff_not,
          Fin.ext_iff] <;>
        omega
    · obtain ⟨middle, _, middle_member⟩ := List.mem_flatMap.mp middle_part
      have middle_bound := middle.isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at middle_member
      rcases middle_member with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
          value_holds, ladder_holds, value_eq, ladder_eq, decide_eq_true_eq, decide_eq_false_iff_not,
          Fin.ext_iff] <;>
        omega

theorem exactly_one_clauses_hold_iff {size : ℕ} (size_positive : 0 < size) {literal_type : Type}
    (value_lit : Fin size → Bool → literal_type)
    (ladder_lit : Fin (size - 1) → Bool → literal_type)
    (literal_holds : literal_type → Prop)
    (value_val : Fin size → Bool) (ladder_val : Fin (size - 1) → Bool)
    (value_holds : ∀ a polarity, literal_holds (value_lit a polarity) ↔ value_val a = polarity)
    (ladder_holds : ∀ i polarity, literal_holds (ladder_lit i polarity) ↔ ladder_val i = polarity) :
    (∀ clause ∈ exactly_one_clauses size value_lit ladder_lit,
        ∃ literal ∈ clause, literal_holds literal) ↔
      ∃ chosen : Fin size,
        (∀ a, value_val a = decide (a = chosen)) ∧
          ∀ i, ladder_val i = decide (i.val < chosen.val) := by
  match size, size_positive, value_lit, ladder_lit, value_val, ladder_val, value_holds, ladder_holds
    with
  | 1, _, value_lit, ladder_lit, value_val, ladder_val, value_holds, _ =>
    exact exactly_one_unit_hold_iff value_lit ladder_lit literal_holds value_val ladder_val value_holds
  | size + 2, _, value_lit, ladder_lit, value_val, ladder_val, value_holds, ladder_holds =>
    exact exactly_one_ladder_hold_iff size value_lit ladder_lit literal_holds value_val ladder_val
      value_holds ladder_holds

end parsimony
