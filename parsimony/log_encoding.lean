import parsimony.extended_definitions
import parsimony.bijection

namespace parsimony

variable {vertex_count : ℕ}

theorem le_two_pow_bit_count (size : ℕ) : size ≤ 2 ^ bit_count size :=
  Nat.le_pow_clog (by norm_num) size

theorem value_bit_at_index (size value index : ℕ) (index_lt : index < bit_count size) :
    value_bit size value (bit_count size - 1 - index) = value.testBit index := by
  unfold value_bit
  congr 1
  omega

theorem eq_of_value_bits_eq (size first second : ℕ) (first_lt : first < 2 ^ bit_count size)
    (second_lt : second < 2 ^ bit_count size)
    (same_bits : ∀ position : Fin (bit_count size),
      value_bit size first position.val = value_bit size second position.val) :
    first = second := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases index_lt : index < bit_count size
  · have bits_equal := same_bits ⟨bit_count size - 1 - index, by omega⟩
    rw [value_bit_at_index size first index index_lt,
      value_bit_at_index size second index index_lt] at bits_equal
    exact bits_equal
  · have pow_le : 2 ^ bit_count size ≤ 2 ^ index := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le first_lt pow_le),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le second_lt pow_le)]

theorem exists_value_with_bits (size : ℕ) (bits : Fin (bit_count size) → Bool) :
    ∃ value, value < 2 ^ bit_count size ∧
      ∀ position : Fin (bit_count size), value_bit size value position.val = bits position := by
  let digits : Fin (bit_count size) → Fin 2 := fun index => if bits (Fin.rev index) then 1 else 0
  refine ⟨(finFunctionFinEquiv digits : ℕ), (finFunctionFinEquiv digits).isLt, ?_⟩
  intro position
  have digit_value : (finFunctionFinEquiv digits : ℕ) / 2 ^ (Fin.rev position : ℕ) % 2 =
      (digits (Fin.rev position) : ℕ) := by
    rw [← finFunctionFinEquiv_symm_apply_val, Equiv.symm_apply_apply]
  have index_eq : bit_count size - 1 - position.val = (Fin.rev position : ℕ) := by
    rw [Fin.val_rev]
    omega
  unfold value_bit
  rw [index_eq, Nat.testBit_eq_decide_div_mod_eq, digit_value]
  simp only [digits, Fin.rev_rev]
  cases bits position <;> simp

theorem exists_first_difference (smaller larger : ℕ) (smaller_lt : smaller < larger) :
    ∃ index, smaller.testBit index = false ∧ larger.testBit index = true ∧
      ∀ later, index < later → smaller.testBit later = larger.testBit later := by
  have xor_ne : smaller ^^^ larger ≠ 0 := by
    intro xor_zero
    have same : smaller = larger := by
      apply Nat.eq_of_testBit_eq
      intro index
      have xor_bit := Nat.testBit_xor smaller larger index
      rw [xor_zero, Nat.zero_testBit] at xor_bit
      revert xor_bit
      cases smaller.testBit index <;> cases larger.testBit index <;> simp
    omega
  obtain ⟨index, top_set, above_clear⟩ := Nat.exists_most_significant_bit xor_ne
  have above_same : ∀ later, index < later → smaller.testBit later = larger.testBit later := by
    intro later later_gt
    have xor_bit := above_clear later later_gt
    rw [Nat.testBit_xor] at xor_bit
    revert xor_bit
    cases smaller.testBit later <;> cases larger.testBit later <;> simp
  rw [Nat.testBit_xor] at top_set
  by_cases smaller_bit : smaller.testBit index = true
  · exfalso
    have larger_bit : larger.testBit index = false := by
      rw [smaller_bit] at top_set
      simpa using top_set
    have larger_lt := Nat.lt_of_testBit index larger_bit smaller_bit
      (fun later later_gt => (above_same later later_gt).symm)
    omega
  · have smaller_false : smaller.testBit index = false := by simpa using smaller_bit
    rw [smaller_false] at top_set
    exact ⟨index, smaller_false, by simpa using top_set, above_same⟩

theorem range_condition_iff (size : ℕ) (size_positive : 0 < size)
    (bits : Fin (bit_count size) → Bool) :
    (∀ position : Fin (bit_count size), value_bit size (size - 1) position.val = false →
      (∃ earlier_position : Fin (bit_count size), earlier_position < position ∧
        bits earlier_position = !value_bit size (size - 1) earlier_position.val) ∨
      bits position = false) ↔
    ∃ value : Fin size, ∀ position : Fin (bit_count size),
      bits position = value_bit size value.val position.val := by
  have last_lt : size - 1 < 2 ^ bit_count size := by
    have := le_two_pow_bit_count size
    omega
  constructor
  · intro range_ok
    obtain ⟨value, value_lt, value_bits⟩ := exists_value_with_bits size bits
    have value_lt_size : value < size := by
      by_contra not_lt
      have last_lt_value : size - 1 < value := by omega
      obtain ⟨index, last_bit, value_bit_set, above_same⟩ :=
        exists_first_difference (size - 1) value last_lt_value
      have index_lt : index < bit_count size := by
        by_contra index_ge
        have pow_le : 2 ^ bit_count size ≤ 2 ^ index :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le value_lt pow_le)] at value_bit_set
        exact absurd value_bit_set (by decide)
      let position : Fin (bit_count size) := ⟨bit_count size - 1 - index, by omega⟩
      have position_last : value_bit size (size - 1) position.val = false := by
        show value_bit size (size - 1) (bit_count size - 1 - index) = false
        rw [value_bit_at_index size (size - 1) index index_lt]
        exact last_bit
      rcases range_ok position position_last with
        ⟨earlier_position, earlier_lt, earlier_bit⟩ | position_bit
      · rw [← value_bits earlier_position] at earlier_bit
        have earlier_val : earlier_position.val < bit_count size - 1 - index := earlier_lt
        have index_gt : index < bit_count size - 1 - earlier_position.val := by omega
        have same := above_same _ index_gt
        unfold value_bit at earlier_bit
        rw [← same] at earlier_bit
        revert earlier_bit
        cases (size - 1).testBit (bit_count size - 1 - earlier_position.val) <;> simp
      · rw [← value_bits position] at position_bit
        have position_value : value_bit size value position.val = value.testBit index := by
          show value_bit size value (bit_count size - 1 - index) = _
          exact value_bit_at_index size value index index_lt
        rw [position_value, value_bit_set] at position_bit
        exact absurd position_bit (by decide)
    exact ⟨⟨value, value_lt_size⟩, fun position => (value_bits position).symm⟩
  · rintro ⟨value, value_bits⟩ position last_false
    by_contra no_clause
    have before_same : ∀ earlier_position : Fin (bit_count size), earlier_position < position →
        bits earlier_position = value_bit size (size - 1) earlier_position.val := by
      intro earlier_position earlier_lt
      have not_flipped : ¬ bits earlier_position =
          !value_bit size (size - 1) earlier_position.val :=
        fun flipped => no_clause (Or.inl ⟨earlier_position, earlier_lt, flipped⟩)
      revert not_flipped
      cases bits earlier_position <;> cases value_bit size (size - 1) earlier_position.val <;> simp
    have position_true : bits position = true := by
      have not_false : ¬ bits position = false := fun is_false => no_clause (Or.inr is_false)
      simpa using not_false
    have value_lt : value.val < 2 ^ bit_count size :=
      lt_of_lt_of_le value.isLt (le_two_pow_bit_count size)
    have last_lt_value : size - 1 < value.val := by
      apply Nat.lt_of_testBit (bit_count size - 1 - position.val)
      · exact last_false
      · exact (value_bits position).symm.trans position_true
      · intro later later_gt
        by_cases later_lt : later < bit_count size
        · let earlier_position : Fin (bit_count size) := ⟨bit_count size - 1 - later, by omega⟩
          have earlier_lt : earlier_position < position := by
            show bit_count size - 1 - later < position.val
            omega
          have last_side := before_same earlier_position earlier_lt
          rw [value_bits earlier_position] at last_side
          have value_side : value_bit size value.val earlier_position.val = value.val.testBit later :=
            value_bit_at_index size value.val later later_lt
          have last_value_side : value_bit size (size - 1) earlier_position.val =
              (size - 1).testBit later :=
            value_bit_at_index size (size - 1) later later_lt
          rw [← value_side, ← last_value_side, last_side]
        · have pow_le : 2 ^ bit_count size ≤ 2 ^ later :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le last_lt pow_le),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le value_lt pow_le)]
    have value_le : value.val ≤ size - 1 := by
      have := value.isLt
      omega
    omega

theorem range_clauses_hold_iff (csp : binary_csp vertex_count) (x : Fin vertex_count)
    (valuation : log_variable csp → Bool) :
    is_model valuation (range_clauses_of_vertex csp x) ↔
      ∀ position : Fin (bit_count (csp.domain_size x)),
        value_bit (csp.domain_size x) (csp.domain_size x - 1) position.val = false →
          (∃ earlier_position : Fin (bit_count (csp.domain_size x)), earlier_position < position ∧
            valuation ⟨x, earlier_position⟩ =
              !value_bit (csp.domain_size x) (csp.domain_size x - 1) earlier_position.val) ∨
          valuation ⟨x, position⟩ = false := by
  constructor
  · intro model position last_false
    have clause_mem : (((List.finRange (bit_count (csp.domain_size x))).filter
          fun earlier_position => decide (earlier_position < position)).map
          (fun earlier_position =>
            ((⟨x, earlier_position⟩ : log_variable csp),
              !value_bit (csp.domain_size x) (csp.domain_size x - 1) earlier_position.val)) ++
        [((⟨x, position⟩ : log_variable csp), false)]) ∈ range_clauses_of_vertex csp x := by
      simp only [range_clauses_of_vertex]
      exact List.mem_map.mpr ⟨position,
        List.mem_filter.mpr ⟨List.mem_finRange position, by simp [last_false]⟩, rfl⟩
    obtain ⟨literal, literal_mem, literal_holds⟩ := model _ clause_mem
    rcases List.mem_append.mp literal_mem with earlier_mem | last_mem
    · obtain ⟨earlier_position, earlier_filter, rfl⟩ := List.mem_map.mp earlier_mem
      left
      exact ⟨earlier_position, by simpa using (List.mem_filter.mp earlier_filter).2, literal_holds⟩
    · rw [List.mem_singleton] at last_mem
      subst last_mem
      right
      exact literal_holds
  · intro condition clause clause_mem
    simp only [range_clauses_of_vertex] at clause_mem
    obtain ⟨position, position_filter, rfl⟩ := List.mem_map.mp clause_mem
    have last_false : value_bit (csp.domain_size x) (csp.domain_size x - 1) position.val = false := by
      simpa using (List.mem_filter.mp position_filter).2
    rcases condition position last_false with
      ⟨earlier_position, earlier_lt, earlier_holds⟩ | last_holds
    · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨earlier_position,
        List.mem_filter.mpr ⟨List.mem_finRange earlier_position, by simpa using earlier_lt⟩, rfl⟩),
        earlier_holds⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), last_holds⟩

theorem range_clauses_hold_iff_code (csp : binary_csp vertex_count) (x : Fin vertex_count)
    (valuation : log_variable csp → Bool) :
    is_model valuation (range_clauses_of_vertex csp x) ↔
      ∃ value : Fin (csp.domain_size x), ∀ position : Fin (bit_count (csp.domain_size x)),
        valuation ⟨x, position⟩ = value_bit (csp.domain_size x) value.val position.val :=
  (range_clauses_hold_iff csp x valuation).trans
    (range_condition_iff (csp.domain_size x) (csp.domain_nonempty x)
      (fun position => valuation ⟨x, position⟩))

theorem blocking_clause_holds_iff (csp : binary_csp vertex_count)
    (valuation : log_variable csp → Bool) (x y : Fin vertex_count)
    (a : Fin (csp.domain_size x)) (b : Fin (csp.domain_size y)) :
    clause_holds valuation (blocking_literals csp x a ++ blocking_literals csp y b) ↔
      ¬ ((∀ position : Fin (bit_count (csp.domain_size x)),
            valuation ⟨x, position⟩ = value_bit (csp.domain_size x) a.val position.val) ∧
          (∀ position : Fin (bit_count (csp.domain_size y)),
            valuation ⟨y, position⟩ = value_bit (csp.domain_size y) b.val position.val)) := by
  constructor
  · rintro ⟨literal, literal_mem, literal_holds⟩ ⟨x_bits, y_bits⟩
    rcases List.mem_append.mp literal_mem with x_mem | y_mem
    · obtain ⟨position, _, rfl⟩ := List.mem_map.mp x_mem
      have holds : valuation ⟨x, position⟩ =
          !value_bit (csp.domain_size x) a.val position.val := literal_holds
      rw [x_bits position] at holds
      revert holds
      cases value_bit (csp.domain_size x) a.val position.val <;> simp
    · obtain ⟨position, _, rfl⟩ := List.mem_map.mp y_mem
      have holds : valuation ⟨y, position⟩ =
          !value_bit (csp.domain_size y) b.val position.val := literal_holds
      rw [y_bits position] at holds
      revert holds
      cases value_bit (csp.domain_size y) b.val position.val <;> simp
  · intro not_both
    by_cases x_bits : ∀ position : Fin (bit_count (csp.domain_size x)),
        valuation ⟨x, position⟩ = value_bit (csp.domain_size x) a.val position.val
    · have not_y : ¬ ∀ position : Fin (bit_count (csp.domain_size y)),
          valuation ⟨y, position⟩ = value_bit (csp.domain_size y) b.val position.val :=
        fun y_bits => not_both ⟨x_bits, y_bits⟩
      obtain ⟨position, differs⟩ := not_forall.mp not_y
      refine ⟨((⟨y, position⟩ : log_variable csp),
          !value_bit (csp.domain_size y) b.val position.val),
        List.mem_append_right _ (List.mem_map.mpr ⟨position, List.mem_finRange position, rfl⟩), ?_⟩
      show valuation ⟨y, position⟩ = !value_bit (csp.domain_size y) b.val position.val
      revert differs
      cases valuation ⟨y, position⟩ <;> cases value_bit (csp.domain_size y) b.val position.val <;>
        simp
    · obtain ⟨position, differs⟩ := not_forall.mp x_bits
      refine ⟨((⟨x, position⟩ : log_variable csp),
          !value_bit (csp.domain_size x) a.val position.val),
        List.mem_append_left _ (List.mem_map.mpr ⟨position, List.mem_finRange position, rfl⟩), ?_⟩
      show valuation ⟨x, position⟩ = !value_bit (csp.domain_size x) a.val position.val
      revert differs
      cases valuation ⟨x, position⟩ <;> cases value_bit (csp.domain_size x) a.val position.val <;>
        simp

theorem log_forbidden_clauses_hold_iff (csp : binary_csp vertex_count)
    (valuation : log_variable csp → Bool) (x y : Fin vertex_count) :
    is_model valuation (log_forbidden_clauses_of_pair csp x y) ↔
      ∀ (a : Fin (csp.domain_size x)) (b : Fin (csp.domain_size y)),
        csp.allowed x y a.val b.val = false →
          ¬ ((∀ position : Fin (bit_count (csp.domain_size x)),
                valuation ⟨x, position⟩ = value_bit (csp.domain_size x) a.val position.val) ∧
              (∀ position : Fin (bit_count (csp.domain_size y)),
                valuation ⟨y, position⟩ = value_bit (csp.domain_size y) b.val position.val)) := by
  constructor
  · intro model a b forbidden
    apply (blocking_clause_holds_iff csp valuation x y a b).mp
    apply model
    exact List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_map.mpr ⟨b,
      List.mem_filter.mpr ⟨List.mem_finRange b, by simp [forbidden]⟩, rfl⟩⟩
  · intro condition clause clause_mem
    obtain ⟨a, _, pair_mem⟩ := List.mem_flatMap.mp clause_mem
    obtain ⟨b, b_filter, rfl⟩ := List.mem_map.mp pair_mem
    have forbidden : csp.allowed x y a.val b.val = false := by
      simpa using (List.mem_filter.mp b_filter).2
    exact (blocking_clause_holds_iff csp valuation x y a b).mpr (condition a b forbidden)

theorem is_model_flatMap_iff {item_type boolean_type : Type} (valuation : boolean_type → Bool)
    (items : List item_type) (clauses_of : item_type → cnf_formula boolean_type) :
    is_model valuation (items.flatMap clauses_of) ↔
      ∀ item ∈ items, is_model valuation (clauses_of item) := by
  constructor
  · intro model item item_mem clause clause_mem
    exact model clause (List.mem_flatMap.mpr ⟨item, item_mem, clause_mem⟩)
  · intro models clause clause_mem
    obtain ⟨item, item_mem, mem⟩ := List.mem_flatMap.mp clause_mem
    exact models item item_mem clause mem

theorem is_model_log_encoding_iff (csp : binary_csp vertex_count)
    (valuation : log_variable csp → Bool) :
    is_model valuation (log_encoding csp) ↔
      (∀ x, ∃ value : Fin (csp.domain_size x), ∀ position : Fin (bit_count (csp.domain_size x)),
        valuation ⟨x, position⟩ = value_bit (csp.domain_size x) value.val position.val) ∧
      ∀ x y, csp.adjacent x y = true →
        ∀ (a : Fin (csp.domain_size x)) (b : Fin (csp.domain_size y)),
          csp.allowed x y a.val b.val = false →
            ¬ ((∀ position : Fin (bit_count (csp.domain_size x)),
                  valuation ⟨x, position⟩ = value_bit (csp.domain_size x) a.val position.val) ∧
                (∀ position : Fin (bit_count (csp.domain_size y)),
                  valuation ⟨y, position⟩ = value_bit (csp.domain_size y) b.val position.val)) := by
  unfold log_encoding
  rw [is_model_append, is_model_flatMap_iff, is_model_clauses_on_chosen_pairs_iff]
  constructor
  · rintro ⟨ranges, pairs⟩
    exact ⟨fun x => (range_clauses_hold_iff_code csp x valuation).mp (ranges x (List.mem_finRange x)),
      fun x y adjacent_x_y => (log_forbidden_clauses_hold_iff csp valuation x y).mp
        (pairs x y adjacent_x_y)⟩
  · rintro ⟨ranges, pairs⟩
    exact ⟨fun x _ => (range_clauses_hold_iff_code csp x valuation).mpr (ranges x),
      fun x y adjacent_x_y => (log_forbidden_clauses_hold_iff csp valuation x y).mpr
        (pairs x y adjacent_x_y)⟩

theorem value_eq_of_bits (csp : binary_csp vertex_count) (x : Fin vertex_count)
    (first second : Fin (csp.domain_size x))
    (same_bits : ∀ position : Fin (bit_count (csp.domain_size x)),
      value_bit (csp.domain_size x) first.val position.val =
        value_bit (csp.domain_size x) second.val position.val) :
    first = second :=
  Fin.ext (eq_of_value_bits_eq (csp.domain_size x) first.val second.val
    (lt_of_lt_of_le first.isLt (le_two_pow_bit_count _))
    (lt_of_lt_of_le second.isLt (le_two_pow_bit_count _)) same_bits)

theorem log_model_iff (csp : binary_csp vertex_count) (valuation : log_variable csp → Bool) :
    is_model valuation (log_encoding csp) ↔
      ∃ candidate, is_solution csp candidate ∧
        valuation = log_valuation_of_assignment csp candidate := by
  rw [is_model_log_encoding_iff]
  constructor
  · rintro ⟨ranges, pairs⟩
    choose candidate candidate_bits using ranges
    have valuation_eq : valuation = log_valuation_of_assignment csp candidate := by
      funext bit_variable
      rcases bit_variable with ⟨x, position⟩
      exact candidate_bits x position
    refine ⟨candidate, ?_, valuation_eq⟩
    intro x y adjacent_x_y
    by_contra not_allowed
    have forbidden : csp.allowed x y (candidate x).val (candidate y).val = false := by
      simpa using not_allowed
    exact pairs x y adjacent_x_y (candidate x) (candidate y) forbidden
      ⟨candidate_bits x, candidate_bits y⟩
  · rintro ⟨candidate, solution, rfl⟩
    refine ⟨fun x => ⟨candidate x, fun position => rfl⟩, ?_⟩
    rintro x y adjacent_x_y a b forbidden ⟨x_bits, y_bits⟩
    have a_is_candidate : a = candidate x :=
      value_eq_of_bits csp x a (candidate x) (fun position => (x_bits position).symm)
    have b_is_candidate : b = candidate y :=
      value_eq_of_bits csp y b (candidate y) (fun position => (y_bits position).symm)
    subst a_is_candidate
    subst b_is_candidate
    have allowed_true := solution x y adjacent_x_y
    rw [forbidden] at allowed_true
    exact absurd allowed_true (by decide)

theorem log_valuation_of_assignment_injective (csp : binary_csp vertex_count) :
    Function.Injective (log_valuation_of_assignment csp) := by
  intro first second same_valuation
  funext x
  exact value_eq_of_bits csp x (first x) (second x)
    (fun position => congrFun same_valuation ⟨x, position⟩)

theorem log_valuation_of_assignment_encodes (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (candidate : assignment csp) :
    log_encodes_tuple csp originals (log_valuation_of_assignment csp candidate)
      (restrict_to_originals csp originals candidate) :=
  fun _ _ => rfl

theorem log_encodes_tuple_unique (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (valuation : log_variable csp → Bool)
    (first second : original_tuple csp originals)
    (encodes_first : log_encodes_tuple csp originals valuation first)
    (encodes_second : log_encodes_tuple csp originals valuation second) :
    first = second := by
  funext x
  exact value_eq_of_bits csp x.val (first x) (second x)
    (fun position => (encodes_first x position).symm.trans (encodes_second x position))

theorem log_model_count (csp : binary_csp vertex_count) :
    model_count (log_encoding csp) =
      Fintype.card {candidate : assignment csp // is_solution csp candidate} := by
  unfold model_count
  symm
  refine Fintype.card_of_bijective
    (f := fun candidate =>
      ⟨log_valuation_of_assignment csp candidate.val,
        (log_model_iff csp _).mpr ⟨candidate.val, candidate.property, rfl⟩⟩) ⟨?_, ?_⟩
  · intro first second same_image
    exact Subtype.ext (log_valuation_of_assignment_injective csp
      (congrArg Subtype.val same_image))
  · rintro ⟨valuation, model⟩
    obtain ⟨candidate, solution, rfl⟩ := (log_model_iff csp _).mp model
    exact ⟨⟨candidate, solution⟩, rfl⟩

theorem log_is_projection_exact_theorem (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) : log_is_projection_exact csp originals := by
  constructor
  · intro valuation model
    obtain ⟨candidate, solution, rfl⟩ := (log_model_iff csp _).mp model
    exact ⟨restrict_to_originals csp originals candidate, ⟨candidate, solution, rfl⟩,
      log_valuation_of_assignment_encodes csp originals candidate⟩
  · rintro tuple ⟨candidate, solution, restricted⟩
    subst restricted
    exact ⟨log_valuation_of_assignment csp candidate,
      (log_model_iff csp _).mpr ⟨candidate, solution, rfl⟩,
      log_valuation_of_assignment_encodes csp originals candidate⟩

theorem log_models_over_tuple_eq_extension_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals) :
    log_models_over_tuple csp originals tuple = extension_count csp originals tuple := by
  unfold log_models_over_tuple extension_count
  symm
  refine Fintype.card_of_bijective
    (f := fun candidate =>
      ⟨log_valuation_of_assignment csp candidate.val,
        (log_model_iff csp _).mpr ⟨candidate.val, candidate.property.1, rfl⟩, by
          have encodes := log_valuation_of_assignment_encodes csp originals candidate.val
          rw [candidate.property.2] at encodes
          exact encodes⟩) ⟨?_, ?_⟩
  · intro first second same_image
    exact Subtype.ext (log_valuation_of_assignment_injective csp
      (congrArg Subtype.val same_image))
  · rintro ⟨valuation, model, encodes⟩
    obtain ⟨candidate, solution, rfl⟩ := (log_model_iff csp _).mp model
    refine ⟨⟨candidate, solution, ?_⟩, rfl⟩
    exact log_encodes_tuple_unique csp originals _ _ _
      (log_valuation_of_assignment_encodes csp originals candidate) encodes

theorem log_parsimonious_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_parsimonious csp originals (log_encoding csp) ↔ has_unique_extension csp originals := by
  have same_count : model_count (log_encoding csp) = model_count (support_encoding csp) := by
    rw [log_model_count, support_model_count]
  unfold is_parsimonious
  rw [same_count]
  exact support_parsimonious_iff csp originals

theorem range_clauses_empty_of_power_of_two (csp : binary_csp vertex_count)
    (x : Fin vertex_count) (exponent : ℕ) (power : csp.domain_size x = 2 ^ exponent) :
    range_clauses_of_vertex csp x = [] := by
  have count_eq : bit_count (csp.domain_size x) = exponent := by
    unfold bit_count
    rw [power]
    exact Nat.clog_pow 2 exponent (by norm_num)
  have all_set : ∀ position : Fin (bit_count (csp.domain_size x)),
      value_bit (csp.domain_size x) (csp.domain_size x - 1) position.val = true := by
    intro position
    have position_lt := position.isLt
    unfold value_bit
    rw [show csp.domain_size x - 1 = 2 ^ exponent - 1 by rw [power],
      Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    omega
  simp [range_clauses_of_vertex, all_set]

theorem blocking_literals_of_single_value (csp : binary_csp vertex_count) (x : Fin vertex_count)
    (single : csp.domain_size x = 1) (value : Fin (csp.domain_size x)) :
    blocking_literals csp x value = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [blocking_literals, List.length_map, List.length_finRange, single]
  simp [bit_count]

theorem empty_clause_of_single_values (csp : binary_csp vertex_count) (x y : Fin vertex_count)
    (x_single : csp.domain_size x = 1) (y_single : csp.domain_size y = 1)
    (forbidden : csp.allowed x y 0 0 = false) :
    [] ∈ log_forbidden_clauses_of_pair csp x y := by
  let a : Fin (csp.domain_size x) := ⟨0, by omega⟩
  let b : Fin (csp.domain_size y) := ⟨0, by omega⟩
  refine List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_map.mpr ⟨b,
    List.mem_filter.mpr ⟨List.mem_finRange b, by simp [a, b, forbidden]⟩, ?_⟩⟩
  rw [blocking_literals_of_single_value csp x x_single, blocking_literals_of_single_value csp y y_single]
  rfl

end parsimony
