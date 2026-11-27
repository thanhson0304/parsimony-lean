import parsimony.ladder
import parsimony.rules.cct_construction

namespace parsimony
namespace rules

open scoped Classical

abbrev boolean := (ℕ × ℕ) ⊕ (ℕ × ℕ)

def before (order : List ℕ) (x y : ℕ) : Prop :=
  List.Sublist [x, y] order

theorem before_cons_iff (head : ℕ) (rest : List ℕ) (x y : ℕ) :
    before (head :: rest) x y ↔ before rest x y ∨ (x = head ∧ y ∈ rest) := by
  unfold before
  constructor
  · intro sublist
    cases sublist with
    | cons _ inner => exact Or.inl inner
    | cons_cons _ inner => exact Or.inr ⟨rfl, List.singleton_sublist.mp inner⟩
  · rintro (inner | ⟨rfl, member⟩)
    · exact inner.cons _
    · exact (List.singleton_sublist.mpr member).cons_cons _

theorem before_mem (order : List ℕ) (x y : ℕ) (x_before : before order x y) : x ∈ order ∧ y ∈ order :=
  ⟨x_before.subset (by simp), x_before.subset (by simp)⟩

theorem before_asymm (order : List ℕ) (nodup : order.Nodup) (x y : ℕ) (x_before : before order x y)
    (y_before : before order y x) : False := by
  induction order with
  | nil => exact absurd (before_mem _ _ _ x_before).1 (by simp)
  | cons head rest hypothesis =>
    obtain ⟨head_new, rest_nodup⟩ := List.nodup_cons.mp nodup
    rw [before_cons_iff] at x_before y_before
    rcases x_before with x_inner | ⟨rfl, y_rest⟩
    · rcases y_before with y_inner | ⟨rfl, x_rest⟩
      · exact hypothesis rest_nodup x_inner y_inner
      · exact head_new (before_mem _ _ _ x_inner).2
    · rcases y_before with y_inner | ⟨rfl, x_rest⟩
      · exact head_new (before_mem _ _ _ y_inner).2
      · exact head_new y_rest

theorem before_trans (order : List ℕ) (nodup : order.Nodup) (x y z : ℕ) (x_before : before order x y)
    (y_before : before order y z) : before order x z := by
  induction order with
  | nil => exact absurd (before_mem _ _ _ x_before).1 (by simp)
  | cons head rest hypothesis =>
    obtain ⟨head_new, rest_nodup⟩ := List.nodup_cons.mp nodup
    rw [before_cons_iff] at x_before y_before ⊢
    rcases x_before with x_inner | ⟨rfl, y_rest⟩
    · rcases y_before with y_inner | ⟨rfl, z_rest⟩
      · exact Or.inl (hypothesis rest_nodup x_inner y_inner)
      · exact absurd (before_mem _ _ _ x_inner).2 head_new
    · rcases y_before with y_inner | ⟨rfl, z_rest⟩
      · exact Or.inr ⟨rfl, (before_mem _ _ _ y_inner).2⟩
      · exact Or.inr ⟨rfl, z_rest⟩

theorem before_total (order : List ℕ) (x y : ℕ) (x_mem : x ∈ order) (y_mem : y ∈ order) (x_ne_y : x ≠ y) :
    before order x y ∨ before order y x := by
  induction order with
  | nil => exact absurd x_mem (by simp)
  | cons head rest hypothesis =>
    rw [before_cons_iff, before_cons_iff]
    rcases List.mem_cons.mp x_mem with rfl | x_rest
    · rcases List.mem_cons.mp y_mem with rfl | y_rest
      · exact absurd rfl x_ne_y
      · exact Or.inl (Or.inr ⟨rfl, y_rest⟩)
    · rcases List.mem_cons.mp y_mem with rfl | y_rest
      · exact Or.inr (Or.inr ⟨rfl, x_rest⟩)
      · rcases hypothesis x_rest y_rest with first | second
        · exact Or.inl (Or.inl first)
        · exact Or.inr (Or.inl second)

theorem before_erase_iff (order : List ℕ) (nodup : order.Nodup) (h x y : ℕ) (x_ne_h : x ≠ h)
    (y_ne_h : y ≠ h) : before (order.erase h) x y ↔ before order x y := by
  constructor
  · intro inner
    exact inner.trans (List.erase_sublist)
  · intro outer
    unfold before at outer ⊢
    rw [nodup.erase_eq_filter]
    have filtered := outer.filter fun z => z != h
    simpa [x_ne_h, y_ne_h] using filtered

def is_tree_order (problem : bct) (order : List ℕ) : Prop :=
  order.Nodup ∧ order.toFinset = problem.vertices ∧ ∀ later ∈ order, order.head? ≠ some later →
    ∃! earlier, problem.edge earlier later ∧ before order earlier later

def root_is_original (problem : bct) (order : List ℕ) : Prop :=
  ∃ root, order.head? = some root ∧ root ∈ problem.originals

def is_listing (problem : bct) (listing : ℕ → List ℕ) : Prop :=
  ∀ x, (listing x).Nodup ∧ (listing x).toFinset = problem.domain x

def is_declared (problem : bct) : boolean → Prop
  | Sum.inl (x, a) => x ∈ problem.vertices ∧ a ∈ problem.domain x
  | Sum.inr (x, position) => x ∈ problem.originals ∧ position + 1 < (problem.domain x).card

def value_at (listing : ℕ → List ℕ) (x : ℕ) (position : Fin (listing x).length) : ℕ :=
  (listing x).get position

def ladder_clauses (listing : ℕ → List ℕ) (x : ℕ) : List (cnf_clause boolean) :=
  exactly_one_clauses (listing x).length
    (fun position polarity => (Sum.inl (x, value_at listing x position), polarity))
    (fun position polarity => (Sum.inr (x, position.val), polarity))

noncomputable def support_clause (problem : bct) (listing : ℕ → List ℕ) (x y a : ℕ) : cnf_clause boolean :=
  (Sum.inl (x, a), false) :: ((listing y).filter fun b => (a, b) ∈ problem.relation x y).map
    fun b => (Sum.inl (y, b), true)

def minimal_support_clauses (problem : bct) (listing : ℕ → List ℕ) (order : List ℕ) :
    Set (cnf_clause boolean) :=
  {clause | (∃ x ∈ problem.originals, clause ∈ ladder_clauses listing x) ∨
    ∃ x y a, problem.edge x y ∧ before order x y ∧ a ∈ problem.domain x ∧
      clause = support_clause problem listing x y a}

def minimal_support_models (problem : bct) (listing : ℕ → List ℕ) (order : List ℕ) :
    Set (boolean → Bool) :=
  {valuation | (∀ declared, ¬ is_declared problem declared → valuation declared = false) ∧
    ∀ clause ∈ minimal_support_clauses problem listing order, clause_holds valuation clause}

def encodes_tuple (problem : bct) (valuation : boolean → Bool) (tuple : ℕ → ℕ) : Prop :=
  ∀ x ∈ problem.originals, ∀ a ∈ problem.domain x, valuation (Sum.inl (x, a)) = decide (a = tuple x)

def minimal_support_models_over (problem : bct) (listing : ℕ → List ℕ) (order : List ℕ)
    (tuple : ℕ → ℕ) : Set (boolean → Bool) :=
  {valuation | valuation ∈ minimal_support_models problem listing order ∧
    encodes_tuple problem valuation tuple}

def is_selection (problem : bct) (order : List ℕ) (tuple : ℕ → ℕ) (selected : ℕ → Finset ℕ) : Prop :=
  (∀ x ∈ problem.vertices, selected x ⊆ problem.domain x) ∧
  (∀ x, x ∉ problem.vertices → selected x = ∅) ∧
  (∀ x ∈ problem.originals, selected x = {tuple x}) ∧
  ∀ x y, problem.edge x y → before order x y → ∀ a ∈ selected x,
    ∃ b ∈ selected y, (a, b) ∈ problem.relation x y

def selections (problem : bct) (order : List ℕ) (tuple : ℕ → ℕ) : Set (ℕ → Finset ℕ) :=
  {selected | is_selection problem order tuple selected}

theorem selections_finite (problem : bct) (order : List ℕ) (tuple : ℕ → ℕ) :
    (selections problem order tuple).Finite := by
  refine Set.Finite.subset (Set.finite_range
    (fun values : ((x : {x // x ∈ problem.vertices}) → {s // s ∈ (problem.domain x.val).powerset}) =>
      fun x : ℕ => if x_mem : x ∈ problem.vertices then (values ⟨x, x_mem⟩).val else ∅)) ?_
  rintro selected ⟨inside, outside, _⟩
  refine ⟨fun x => ⟨selected x.val, Finset.mem_powerset.mpr (inside x.val x.property)⟩, ?_⟩
  funext x
  by_cases x_mem : x ∈ problem.vertices
  · simp [x_mem]
  · simp [x_mem, outside x x_mem]

noncomputable def valuation_of_selection (problem : bct) (listing : ℕ → List ℕ) (tuple : ℕ → ℕ)
    (selected : ℕ → Finset ℕ) : boolean → Bool
  | Sum.inl (x, a) => decide (a ∈ selected x)
  | Sum.inr (x, position) => decide (x ∈ problem.originals ∧ position + 1 < (problem.domain x).card ∧
      position < (listing x).idxOf (tuple x))

theorem ladder_holds_iff (problem : bct) (listing : ℕ → List ℕ) (is_listing_listing : is_listing problem listing)
    (x : ℕ) (nonempty : (problem.domain x).Nonempty) (valuation : boolean → Bool) :
    (∀ clause ∈ ladder_clauses listing x, clause_holds valuation clause) ↔
      ∃ chosen : Fin (listing x).length,
        (∀ position, valuation (Sum.inl (x, value_at listing x position)) = decide (position = chosen)) ∧
        ∀ position : Fin ((listing x).length - 1),
          valuation (Sum.inr (x, position.val)) = decide (position.val < chosen.val) := by
  have positive : 0 < (listing x).length := by
    obtain ⟨a, a_mem⟩ := nonempty
    rw [← (is_listing_listing x).2, List.mem_toFinset] at a_mem
    exact List.length_pos_of_mem a_mem
  exact exactly_one_clauses_hold_iff positive _ _ (fun literal : cnf_literal boolean => valuation literal.1 = literal.2)
    (fun position => valuation (Sum.inl (x, value_at listing x position)))
    (fun position => valuation (Sum.inr (x, position.val))) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

theorem listing_length (problem : bct) (listing : ℕ → List ℕ) (is_listing_listing : is_listing problem listing)
    (x : ℕ) : (listing x).length = (problem.domain x).card := by
  rw [← (is_listing_listing x).2, List.toFinset_card_of_nodup (is_listing_listing x).1]

theorem mem_listing (problem : bct) (listing : ℕ → List ℕ) (is_listing_listing : is_listing problem listing)
    (x a : ℕ) : a ∈ listing x ↔ a ∈ problem.domain x := by
  rw [← (is_listing_listing x).2, List.mem_toFinset]

theorem support_clause_holds_iff (problem : bct) (listing : ℕ → List ℕ)
    (is_listing_listing : is_listing problem listing) (x y a : ℕ) (valuation : boolean → Bool) :
    clause_holds valuation (support_clause problem listing x y a) ↔
      (valuation (Sum.inl (x, a)) = true →
        ∃ b ∈ problem.domain y, (a, b) ∈ problem.relation x y ∧ valuation (Sum.inl (y, b)) = true) := by
  unfold clause_holds support_clause
  simp only [List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨literal, rfl | ⟨b, ⟨b_mem, allowed⟩, rfl⟩, holds⟩ selected
    · simp only at holds
      rw [selected] at holds
      exact absurd holds (by decide)
    · exact ⟨b, (mem_listing problem listing is_listing_listing y b).mp b_mem, allowed, holds⟩
  · intro supported
    by_cases selected : valuation (Sum.inl (x, a)) = true
    · obtain ⟨b, b_mem, allowed, holds⟩ := supported selected
      exact ⟨_, Or.inr ⟨b, ⟨(mem_listing problem listing is_listing_listing y b).mpr b_mem, allowed⟩,
        rfl⟩, holds⟩
    · exact ⟨_, Or.inl rfl, by simpa using selected⟩

theorem minimal_support_models_eq_image (problem : bct) (listing : ℕ → List ℕ)
    (is_listing_listing : is_listing problem listing)
    (nonempty : ∀ x ∈ problem.originals, (problem.domain x).Nonempty) (order : List ℕ) (tuple : ℕ → ℕ) :
    minimal_support_models_over problem listing order tuple =
      valuation_of_selection problem listing tuple '' selections problem order tuple := by
  ext valuation
  constructor
  · rintro ⟨⟨undeclared, holds⟩, encodes⟩
    have ladder_at : ∀ x ∈ problem.originals, ∃ chosen : Fin (listing x).length,
        (∀ position, valuation (Sum.inl (x, value_at listing x position)) = decide (position = chosen)) ∧
        ∀ position : Fin ((listing x).length - 1),
          valuation (Sum.inr (x, position.val)) = decide (position.val < chosen.val) := by
      intro x x_original
      exact (ladder_holds_iff problem listing is_listing_listing x (nonempty x x_original) valuation).mp
        fun clause clause_mem => holds clause (Or.inl ⟨x, x_original, clause_mem⟩)
    have chosen_value : ∀ x ∈ problem.originals, ∀ chosen : Fin (listing x).length,
        (∀ position, valuation (Sum.inl (x, value_at listing x position)) = decide (position = chosen)) →
        value_at listing x chosen = tuple x := by
      intro x x_original chosen at_values
      have member : value_at listing x chosen ∈ problem.domain x :=
        (mem_listing problem listing is_listing_listing x _).mp (List.get_mem _ _)
      have selected := at_values chosen
      rw [encodes x x_original _ member] at selected
      simpa using selected
    let selected : ℕ → Finset ℕ := fun x =>
      if x ∈ problem.vertices then
        (problem.domain x).filter fun a => valuation (Sum.inl (x, a)) = true else ∅
    have mem_selected : ∀ x a, a ∈ selected x ↔ valuation (Sum.inl (x, a)) = true := by
      intro x a
      by_cases declared : is_declared problem (Sum.inl (x, a))
      · have x_vertex : x ∈ problem.vertices := declared.1
        have a_mem : a ∈ problem.domain x := declared.2
        simp [selected, x_vertex, a_mem]
      · have off := undeclared _ declared
        rw [off]
        simp only [Bool.false_eq_true, iff_false]
        intro member
        by_cases x_vertex : x ∈ problem.vertices
        · simp only [selected, x_vertex, ite_true, Finset.mem_filter] at member
          exact declared ⟨x_vertex, member.1⟩
        · simp [selected, x_vertex] at member
    refine ⟨selected, ⟨fun x x_vertex => ?_, fun x x_out => ?_, fun x x_original => ?_,
      fun x y edge_x_y x_before a a_selected => ?_⟩, ?_⟩
    · simp only [selected, x_vertex, ite_true]
      exact Finset.filter_subset _ _
    · simp [selected, x_out]
    · obtain ⟨chosen, at_values, _⟩ := ladder_at x x_original
      have tuple_is := chosen_value x x_original chosen at_values
      have tuple_mem : tuple x ∈ problem.domain x := by
        rw [← tuple_is]
        exact (mem_listing problem listing is_listing_listing x _).mp (List.get_mem _ _)
      ext a
      rw [mem_selected, Finset.mem_singleton]
      by_cases a_mem : a ∈ problem.domain x
      · rw [encodes x x_original a a_mem]
        simp
      · have off := undeclared (Sum.inl (x, a)) fun declared => a_mem declared.2
        rw [off]
        simp only [Bool.false_eq_true, false_iff]
        rintro rfl
        exact a_mem tuple_mem
    · have a_mem : a ∈ problem.domain x := by
        have x_vertex := problem.edge_vertices x y edge_x_y
        simp only [selected, x_vertex, ite_true, Finset.mem_filter] at a_selected
        exact a_selected.1
      have clause := holds _ (Or.inr ⟨x, y, a, edge_x_y, x_before, a_mem, rfl⟩)
      obtain ⟨b, _, allowed, b_selected⟩ := (support_clause_holds_iff problem listing is_listing_listing
        x y a valuation).mp clause ((mem_selected x a).mp a_selected)
      exact ⟨b, (mem_selected y b).mpr b_selected, allowed⟩
    · funext declared
      rcases declared with ⟨x, a⟩ | ⟨x, position⟩
      · simp only [valuation_of_selection]
        by_cases on : valuation (Sum.inl (x, a)) = true
        · rw [on]
          simpa using (mem_selected x a).mpr on
        · have off : valuation (Sum.inl (x, a)) = false := by simpa using on
          rw [off]
          simpa using fun member => on ((mem_selected x a).mp member)
      · simp only [valuation_of_selection]
        by_cases is_declared_ladder : x ∈ problem.originals ∧ position + 1 < (problem.domain x).card
        · obtain ⟨x_original, in_range⟩ := is_declared_ladder
          obtain ⟨chosen, at_values, at_ladders⟩ := ladder_at x x_original
          have tuple_is := chosen_value x x_original chosen at_values
          have index : (listing x).idxOf (tuple x) = chosen.val := by
            rw [← tuple_is]
            exact (is_listing_listing x).1.idxOf_getElem chosen.val chosen.isLt
          have length_is := listing_length problem listing is_listing_listing x
          have stated := at_ladders ⟨position, by omega⟩
          rw [stated, index]
          simp [x_original, in_range]
        · have off := undeclared (Sum.inr (x, position)) is_declared_ladder
          rw [off]
          simp only [decide_eq_false_iff_not]
          intro all
          exact is_declared_ladder ⟨all.1, all.2.1⟩
  · rintro ⟨selected, ⟨inside, outside, at_originals, supported⟩, rfl⟩
    refine ⟨⟨fun declared not_declared => ?_, fun clause clause_mem => ?_⟩, fun x x_original a _ => ?_⟩
    · rcases declared with ⟨x, a⟩ | ⟨x, position⟩
      · simp only [valuation_of_selection, decide_eq_false_iff_not]
        intro member
        by_cases x_vertex : x ∈ problem.vertices
        · exact not_declared ⟨x_vertex, inside x x_vertex member⟩
        · rw [outside x x_vertex] at member
          exact absurd member (Finset.notMem_empty _)
      · simp only [valuation_of_selection, decide_eq_false_iff_not]
        intro all
        exact not_declared ⟨all.1, all.2.1⟩
    · rcases clause_mem with ⟨x, x_original, in_ladder⟩ | ⟨x, y, a, edge_x_y, x_before, a_mem, rfl⟩
      · have x_vertex := problem.originals_subset x_original
        have tuple_mem : tuple x ∈ problem.domain x := by
          apply inside x x_vertex
          rw [at_originals x x_original]
          exact Finset.mem_singleton_self _
        have in_list : tuple x ∈ listing x :=
          (mem_listing problem listing is_listing_listing x _).mpr tuple_mem
        refine (ladder_holds_iff problem listing is_listing_listing x (nonempty x x_original) _).mpr
          ⟨⟨(listing x).idxOf (tuple x), List.idxOf_lt_length_of_mem in_list⟩, fun position => ?_,
            fun position => ?_⟩ clause in_ladder
        · simp only [valuation_of_selection, at_originals x x_original, Finset.mem_singleton]
          congr 1
          rw [eq_iff_iff]
          constructor
          · intro same
            apply Fin.ext
            simp only
            rw [← same]
            exact ((is_listing_listing x).1.idxOf_getElem position.val position.isLt).symm
          · intro same
            rw [same]
            exact List.getElem_idxOf (List.idxOf_lt_length_of_mem in_list)
        · have length_is := listing_length problem listing is_listing_listing x
          have in_range : position.val + 1 < (problem.domain x).card := by
            have := position.isLt
            omega
          simp [valuation_of_selection, x_original, in_range]
      · rw [support_clause_holds_iff problem listing is_listing_listing]
        intro on
        have a_selected : a ∈ selected x := by simpa [valuation_of_selection] using on
        obtain ⟨b, b_selected, allowed⟩ := supported x y edge_x_y x_before a a_selected
        refine ⟨b, inside y (edge_vertices_right problem x y edge_x_y) b_selected, allowed, ?_⟩
        simpa [valuation_of_selection] using b_selected
    · simp only [valuation_of_selection, at_originals x x_original, Finset.mem_singleton]

theorem minimal_support_count_eq_selections (problem : bct) (listing : ℕ → List ℕ)
    (is_listing_listing : is_listing problem listing)
    (nonempty : ∀ x ∈ problem.originals, (problem.domain x).Nonempty) (order : List ℕ) (tuple : ℕ → ℕ) :
    (minimal_support_models_over problem listing order tuple).ncard =
      (selections problem order tuple).ncard := by
  rw [minimal_support_models_eq_image problem listing is_listing_listing nonempty order tuple]
  refine Set.InjOn.ncard_image fun first _ second _ same => ?_
  funext x
  ext a
  have at_literal := congrFun same (Sum.inl (x, a))
  simp only [valuation_of_selection, decide_eq_decide] at at_literal
  exact at_literal

end rules
end parsimony
