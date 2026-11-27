import parsimony.rules.rule_four

namespace parsimony
namespace rules

open scoped Classical

def agree_outside (pivot : ℕ) (first second : Finset (ℕ × ℕ)) : Prop :=
  (∀ literal ∈ first \ second, literal.1 = pivot) ∧ ∀ literal ∈ second \ first, literal.1 = pivot

theorem agree_outside_iff (pivot : ℕ) (first second : Finset (ℕ × ℕ)) :
    agree_outside pivot first second ↔
      ∀ literal : ℕ × ℕ, literal.1 ≠ pivot → (literal ∈ first ↔ literal ∈ second) := by
  unfold agree_outside
  constructor
  · rintro ⟨forward, backward⟩ literal off_pivot
    constructor
    · intro in_first
      by_contra not_second
      exact off_pivot (forward literal (Finset.mem_sdiff.mpr ⟨in_first, not_second⟩))
    · intro in_second
      by_contra not_first
      exact off_pivot (backward literal (Finset.mem_sdiff.mpr ⟨in_second, not_first⟩))
  · intro same
    constructor
    · intro literal member
      obtain ⟨in_first, not_second⟩ := Finset.mem_sdiff.mp member
      by_contra off_pivot
      exact not_second ((same literal off_pivot).mp in_first)
    · intro literal member
      obtain ⟨in_second, not_first⟩ := Finset.mem_sdiff.mp member
      by_contra off_pivot
      exact not_first ((same literal off_pivot).mpr in_second)

theorem agree_outside_equivalence (pivot : ℕ) : Equivalence (agree_outside pivot) := by
  constructor
  · intro box
    exact (agree_outside_iff pivot box box).mpr fun _ _ => Iff.rfl
  · intro first second agree
    exact ⟨agree.2, agree.1⟩
  · intro first second third first_second second_third
    rw [agree_outside_iff] at *
    exact fun literal off_pivot =>
      (first_second literal off_pivot).trans (second_third literal off_pivot)

noncomputable def class_of (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ) (box : Finset (ℕ × ℕ)) :
    Finset (Finset (ℕ × ℕ)) :=
  table.filter (agree_outside pivot box)

noncomputable def merged_box (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ) (box : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  (class_of table pivot box).biUnion id

noncomputable def merge (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  table.image (merged_box table pivot)

theorem mem_merged_box (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ) (box : Finset (ℕ × ℕ))
    (literal : ℕ × ℕ) : literal ∈ merged_box table pivot box ↔
      ∃ other ∈ table, agree_outside pivot box other ∧ literal ∈ other := by
  simp only [merged_box, class_of, Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨other, ⟨other_mem, agree⟩, literal_mem⟩
    exact ⟨other, other_mem, agree, literal_mem⟩
  · rintro ⟨other, other_mem, agree, literal_mem⟩
    exact ⟨other, ⟨other_mem, agree⟩, literal_mem⟩

theorem merged_box_congr (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ)
    (first second : Finset (ℕ × ℕ)) (agree : agree_outside pivot first second) :
    merged_box table pivot first = merged_box table pivot second := by
  ext literal
  rw [mem_merged_box, mem_merged_box]
  refine exists_congr fun other => and_congr_right fun _ => and_congr_left fun _ => ?_
  have equivalence := agree_outside_equivalence pivot
  exact ⟨fun first_other => equivalence.trans (equivalence.symm agree) first_other,
    fun second_other => equivalence.trans agree second_other⟩

theorem merged_box_fits_iff (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ)
    (box : Finset (ℕ × ℕ)) (box_mem : box ∈ table) (neighbours : ℕ → ℕ) :
    box_fits problem h (merged_box table pivot box) neighbours ↔
      ∃ other ∈ class_of table pivot box, box_fits problem h other neighbours := by
  have equivalence := agree_outside_equivalence pivot
  constructor
  · intro fits
    have off_pivot : ∀ other ∈ class_of table pivot box, ∀ y, problem.edge h y → y ≠ pivot →
        (y, neighbours y) ∈ other := by
      intro other other_mem y edge_h_y y_ne
      obtain ⟨_, agree⟩ := Finset.mem_filter.mp other_mem
      obtain ⟨witness, _, witness_agree, witness_literal⟩ :=
        (mem_merged_box table pivot box _).mp (fits y edge_h_y)
      have witness_other := equivalence.trans (equivalence.symm witness_agree) agree
      exact ((agree_outside_iff pivot witness other).mp witness_other (y, neighbours y) y_ne).mp
        witness_literal
    by_cases edge_h_pivot : problem.edge h pivot
    · obtain ⟨witness, witness_mem, witness_agree, witness_literal⟩ :=
        (mem_merged_box table pivot box _).mp (fits pivot edge_h_pivot)
      have in_class : witness ∈ class_of table pivot box :=
        Finset.mem_filter.mpr ⟨witness_mem, witness_agree⟩
      refine ⟨witness, in_class, fun y edge_h_y => ?_⟩
      by_cases y_is_pivot : y = pivot
      · subst y_is_pivot
        exact witness_literal
      · exact off_pivot witness in_class y edge_h_y y_is_pivot
    · have in_class : box ∈ class_of table pivot box :=
        Finset.mem_filter.mpr ⟨box_mem, equivalence.refl box⟩
      refine ⟨box, in_class, fun y edge_h_y => ?_⟩
      refine off_pivot box in_class y edge_h_y ?_
      rintro rfl
      exact edge_h_pivot edge_h_y
  · rintro ⟨other, other_mem, fits⟩ y edge_h_y
    obtain ⟨other_in_table, agree⟩ := Finset.mem_filter.mp other_mem
    exact (mem_merged_box table pivot box _).mpr ⟨other, other_in_table, agree, fits y edge_h_y⟩

theorem merge_represents_iff (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ)
    (neighbours : ℕ → ℕ) : (∃ box ∈ merge table pivot, box_fits problem h box neighbours) ↔
      ∃ box ∈ table, box_fits problem h box neighbours := by
  constructor
  · rintro ⟨merged, merged_mem, fits⟩
    obtain ⟨box, box_mem, rfl⟩ := Finset.mem_image.mp merged_mem
    obtain ⟨other, other_mem, other_fits⟩ :=
      (merged_box_fits_iff problem h table pivot box box_mem neighbours).mp fits
    exact ⟨other, (Finset.mem_filter.mp other_mem).1, other_fits⟩
  · rintro ⟨box, box_mem, fits⟩
    refine ⟨merged_box table pivot box, Finset.mem_image_of_mem _ box_mem, ?_⟩
    exact (merged_box_fits_iff problem h table pivot box box_mem neighbours).mpr
      ⟨box, Finset.mem_filter.mpr ⟨box_mem, (agree_outside_equivalence pivot).refl box⟩, fits⟩

theorem merge_count_le (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ))) (pivot : ℕ)
    (neighbours : ℕ → ℕ) :
    box_count problem h (merge table pivot) neighbours ≤ box_count problem h table neighbours := by
  unfold box_count
  refine le_trans (Finset.card_le_card (t := (table.filter fun box =>
    box_fits problem h box neighbours).image (merged_box table pivot)) ?_) Finset.card_image_le
  intro merged merged_mem
  obtain ⟨in_merge, fits⟩ := Finset.mem_filter.mp merged_mem
  obtain ⟨box, box_mem, rfl⟩ := Finset.mem_image.mp in_merge
  obtain ⟨other, other_mem, other_fits⟩ :=
    (merged_box_fits_iff problem h table pivot box box_mem neighbours).mp fits
  obtain ⟨other_in_table, agree⟩ := Finset.mem_filter.mp other_mem
  refine Finset.mem_image.mpr ⟨other, Finset.mem_filter.mpr ⟨other_in_table, other_fits⟩, ?_⟩
  exact (merged_box_congr table pivot box other agree).symm

noncomputable def merge_along (start : Finset (Finset (ℕ × ℕ))) (pivots : List ℕ) :
    Finset (Finset (ℕ × ℕ)) :=
  pivots.foldl merge start

theorem merge_along_represents_iff (problem : bct) (h : ℕ) (pivots : List ℕ)
    (start : Finset (Finset (ℕ × ℕ))) (neighbours : ℕ → ℕ) :
    (∃ box ∈ merge_along start pivots, box_fits problem h box neighbours) ↔
      ∃ box ∈ start, box_fits problem h box neighbours := by
  induction pivots generalizing start with
  | nil => exact Iff.rfl
  | cons pivot later hypothesis =>
    exact (hypothesis (merge start pivot)).trans (merge_represents_iff problem h start pivot neighbours)

theorem merge_along_count_le (problem : bct) (h : ℕ) (pivots : List ℕ)
    (start : Finset (Finset (ℕ × ℕ))) (neighbours : ℕ → ℕ) :
    box_count problem h (merge_along start pivots) neighbours ≤
      box_count problem h start neighbours := by
  induction pivots generalizing start with
  | nil => exact le_rfl
  | cons pivot later hypothesis =>
    exact (hypothesis (merge start pivot)).trans (merge_count_le problem h start pivot neighbours)

noncomputable def neighbour_set (problem : bct) (h : ℕ) : Finset ℕ :=
  problem.vertices.filter (problem.edge h)

theorem mem_neighbour_set (problem : bct) (h y : ℕ) :
    y ∈ neighbour_set problem h ↔ problem.edge h y := by
  simp only [neighbour_set, Finset.mem_filter]
  exact ⟨fun both => both.2, fun edge_h_y => ⟨edge_vertices_right problem h y edge_h_y, edge_h_y⟩⟩

noncomputable def value_box (problem : bct) (h a : ℕ) : Finset (ℕ × ℕ) :=
  (neighbour_set problem h).biUnion fun y =>
    ((problem.relation h y).filter fun pair => pair.1 = a).image fun pair => (y, pair.2)

theorem mem_value_box (problem : bct) (h a y b : ℕ) :
    (y, b) ∈ value_box problem h a ↔ problem.edge h y ∧ (a, b) ∈ problem.relation h y := by
  simp only [value_box, Finset.mem_biUnion, mem_neighbour_set, Finset.mem_image, Finset.mem_filter,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨z, edge_h_z, c, d, ⟨member, rfl⟩, rfl, rfl⟩
    exact ⟨edge_h_z, member⟩
  · rintro ⟨edge_h_y, member⟩
    exact ⟨y, edge_h_y, a, b, ⟨member, rfl⟩, rfl, rfl⟩

noncomputable def value_table (problem : bct) (h : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (problem.domain h).image (value_box problem h)

theorem value_box_fits_iff (problem : bct) (h a : ℕ) (neighbours : ℕ → ℕ) :
    box_fits problem h (value_box problem h a) neighbours ↔ value_fits problem h a neighbours := by
  refine forall_congr' fun y => imp_congr_right fun edge_h_y => ?_
  rw [mem_value_box]
  exact ⟨fun both => both.2, fun member => ⟨edge_h_y, member⟩⟩

theorem value_table_represents_iff (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ) :
    (∃ box ∈ value_table problem h, box_fits problem h box neighbours) ↔
      ∃ a ∈ problem.domain h, value_fits problem h a neighbours := by
  constructor
  · rintro ⟨box, box_mem, fits⟩
    obtain ⟨a, a_mem, rfl⟩ := Finset.mem_image.mp box_mem
    exact ⟨a, a_mem, (value_box_fits_iff problem h a neighbours).mp fits⟩
  · rintro ⟨a, a_mem, fits⟩
    exact ⟨value_box problem h a, Finset.mem_image_of_mem _ a_mem,
      (value_box_fits_iff problem h a neighbours).mpr fits⟩

theorem value_table_count_le (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ) :
    box_count problem h (value_table problem h) neighbours ≤ old_value_count problem h neighbours := by
  unfold box_count old_value_count
  refine le_trans (Finset.card_le_card (t := ((problem.domain h).filter fun a =>
    value_fits problem h a neighbours).image (value_box problem h)) ?_) Finset.card_image_le
  intro box box_mem
  obtain ⟨in_table, fits⟩ := Finset.mem_filter.mp box_mem
  obtain ⟨a, a_mem, rfl⟩ := Finset.mem_image.mp in_table
  exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨a_mem,
    (value_box_fits_iff problem h a neighbours).mp fits⟩, rfl⟩

noncomputable def tuple_box (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (neighbour_set problem h).image fun y => (y, neighbours y)

theorem mem_tuple_box (problem : bct) (h y b : ℕ) (neighbours : ℕ → ℕ) :
    (y, b) ∈ tuple_box problem h neighbours ↔ problem.edge h y ∧ b = neighbours y := by
  simp only [tuple_box, Finset.mem_image, mem_neighbour_set, Prod.mk.injEq]
  constructor
  · rintro ⟨z, edge_h_z, rfl, rfl⟩
    exact ⟨edge_h_z, rfl⟩
  · rintro ⟨edge_h_y, rfl⟩
    exact ⟨y, edge_h_y, rfl, rfl⟩

noncomputable def current_literals (problem : bct) (h : ℕ) : Finset (ℕ × ℕ) :=
  (neighbour_set problem h).biUnion fun y => (problem.domain y).image fun b => (y, b)

noncomputable def tuple_table (problem : bct) (h : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (current_literals problem h).powerset.filter fun box => ∃ neighbours, is_current problem h neighbours ∧
    (∃ a ∈ problem.domain h, value_fits problem h a neighbours) ∧ box = tuple_box problem h neighbours

theorem mem_tuple_table (problem : bct) (h : ℕ) (box : Finset (ℕ × ℕ)) :
    box ∈ tuple_table problem h ↔ ∃ neighbours, is_current problem h neighbours ∧
      (∃ a ∈ problem.domain h, value_fits problem h a neighbours) ∧
        box = tuple_box problem h neighbours := by
  simp only [tuple_table, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  rintro ⟨neighbours, current, _, rfl⟩
  intro literal literal_mem
  obtain ⟨y, b⟩ := literal
  obtain ⟨edge_h_y, rfl⟩ := (mem_tuple_box problem h y b neighbours).mp literal_mem
  exact Finset.mem_biUnion.mpr ⟨y, (mem_neighbour_set problem h y).mpr edge_h_y,
    Finset.mem_image_of_mem _ (current y edge_h_y)⟩

theorem tuple_box_fits (problem : bct) (h : ℕ) (center neighbours : ℕ → ℕ)
    (fits : box_fits problem h (tuple_box problem h center) neighbours) :
    ∀ y, problem.edge h y → neighbours y = center y :=
  fun y edge_h_y => ((mem_tuple_box problem h y _ center).mp (fits y edge_h_y)).2

theorem tuple_box_congr (problem : bct) (h : ℕ) (first second : ℕ → ℕ)
    (same : ∀ y, problem.edge h y → first y = second y) :
    tuple_box problem h first = tuple_box problem h second := by
  ext ⟨y, b⟩
  rw [mem_tuple_box, mem_tuple_box]
  exact and_congr_right fun edge_h_y => by rw [same y edge_h_y]

theorem value_fits_congr (problem : bct) (h a : ℕ) (first second : ℕ → ℕ)
    (same : ∀ y, problem.edge h y → first y = second y) (fits : value_fits problem h a first) :
    value_fits problem h a second := by
  intro y edge_h_y
  rw [← same y edge_h_y]
  exact fits y edge_h_y

theorem tuple_table_represents_iff (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ)
    (current : is_current problem h neighbours) :
    (∃ box ∈ tuple_table problem h, box_fits problem h box neighbours) ↔
      ∃ a ∈ problem.domain h, value_fits problem h a neighbours := by
  constructor
  · rintro ⟨box, box_mem, fits⟩
    obtain ⟨center, _, ⟨a, a_mem, a_fits⟩, rfl⟩ := (mem_tuple_table problem h box).mp box_mem
    have same := tuple_box_fits problem h center neighbours fits
    exact ⟨a, a_mem, value_fits_congr problem h a center neighbours
      (fun y edge_h_y => (same y edge_h_y).symm) a_fits⟩
  · intro compatible
    refine ⟨tuple_box problem h neighbours, (mem_tuple_table problem h _).mpr
      ⟨neighbours, current, compatible, rfl⟩, fun y edge_h_y => ?_⟩
    exact (mem_tuple_box problem h y _ neighbours).mpr ⟨edge_h_y, rfl⟩

theorem tuple_table_count_le_one (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ) :
    box_count problem h (tuple_table problem h) neighbours ≤ 1 := by
  unfold box_count
  refine Finset.card_le_one.mpr fun first first_mem second second_mem => ?_
  obtain ⟨first_in, first_fits⟩ := Finset.mem_filter.mp first_mem
  obtain ⟨second_in, second_fits⟩ := Finset.mem_filter.mp second_mem
  obtain ⟨first_center, _, _, rfl⟩ := (mem_tuple_table problem h first).mp first_in
  obtain ⟨second_center, _, _, rfl⟩ := (mem_tuple_table problem h second).mp second_in
  refine tuple_box_congr problem h first_center second_center fun y edge_h_y => ?_
  rw [← tuple_box_fits problem h first_center neighbours first_fits y edge_h_y,
    ← tuple_box_fits problem h second_center neighbours second_fits y edge_h_y]

theorem tuple_table_count_le (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ)
    (current : is_current problem h neighbours) :
    box_count problem h (tuple_table problem h) neighbours ≤ old_value_count problem h neighbours := by
  by_cases none : box_count problem h (tuple_table problem h) neighbours = 0
  · omega
  · have represented : ∃ box ∈ tuple_table problem h, box_fits problem h box neighbours := by
      have positive := Nat.pos_of_ne_zero none
      unfold box_count at positive
      rw [Finset.card_pos, Finset.filter_nonempty_iff] at positive
      exact positive
    have compatible := (tuple_table_represents_iff problem h neighbours current).mp represented
    have old_positive : 0 < old_value_count problem h neighbours := by
      unfold old_value_count
      rw [Finset.card_pos, Finset.filter_nonempty_iff]
      exact compatible
    have at_most_one := tuple_table_count_le_one problem h neighbours
    omega

noncomputable def construction_start (problem : bct) (h first_pivot : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  if ∏ y ∈ (neighbour_set problem h).erase first_pivot, (problem.domain y).card <
      (problem.domain h).card
  then merge (tuple_table problem h) first_pivot else value_table problem h

def is_aaai_construction (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ))) : Prop :=
  ∃ first_pivot ∈ neighbour_set problem h,
    (∀ y ∈ neighbour_set problem h, (problem.domain y).card ≤ (problem.domain first_pivot).card) ∧
    ∃ pivots : List ℕ, pivots.Nodup ∧ pivots.toFinset = neighbour_set problem h ∧
      pivots.Pairwise (fun y z => (problem.domain z).card ≤ (problem.domain y).card) ∧
      table = merge_along (construction_start problem h first_pivot) pivots

theorem construction_start_count_le (problem : bct) (h first_pivot : ℕ) (neighbours : ℕ → ℕ)
    (current : is_current problem h neighbours) :
    box_count problem h (construction_start problem h first_pivot) neighbours ≤
      old_value_count problem h neighbours := by
  unfold construction_start
  split_ifs
  · exact (merge_count_le problem h _ first_pivot neighbours).trans
      (tuple_table_count_le problem h neighbours current)
  · exact value_table_count_le problem h neighbours

theorem construction_start_represents_iff (problem : bct) (h first_pivot : ℕ) (neighbours : ℕ → ℕ)
    (current : is_current problem h neighbours) :
    (∃ box ∈ construction_start problem h first_pivot, box_fits problem h box neighbours) ↔
      ∃ a ∈ problem.domain h, value_fits problem h a neighbours := by
  unfold construction_start
  split_ifs
  · exact (merge_represents_iff problem h _ first_pivot neighbours).trans
      (tuple_table_represents_iff problem h neighbours current)
  · exact value_table_represents_iff problem h neighbours

theorem construction_is_valid (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (construction : is_aaai_construction problem h table) : is_valid_table problem h table := by
  obtain ⟨first_pivot, _, _, pivots, _, _, _, rfl⟩ := construction
  intro neighbours current
  exact ((merge_along_represents_iff problem h pivots _ neighbours).trans
    (construction_start_represents_iff problem h first_pivot neighbours current)).symm

theorem construction_count_le (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (construction : is_aaai_construction problem h table) (neighbours : ℕ → ℕ)
    (current : is_current problem h neighbours) :
    box_count problem h table neighbours ≤ old_value_count problem h neighbours := by
  obtain ⟨first_pivot, _, _, pivots, _, _, _, rfl⟩ := construction
  exact (merge_along_count_le problem h pivots _ neighbours).trans
    (construction_start_count_le problem h first_pivot neighbours current)

theorem tuple_start_count_eq_one (problem : bct) (h first_pivot : ℕ) (pivots : List ℕ)
    (neighbours : ℕ → ℕ) (current : is_current problem h neighbours)
    (compatible : ∃ a ∈ problem.domain h, value_fits problem h a neighbours) :
    box_count problem h (merge_along (merge (tuple_table problem h) first_pivot) pivots) neighbours
      = 1 := by
  have upper : box_count problem h (merge_along (merge (tuple_table problem h) first_pivot) pivots)
      neighbours ≤ 1 :=
    (merge_along_count_le problem h pivots _ neighbours).trans
      ((merge_count_le problem h _ first_pivot neighbours).trans
        (tuple_table_count_le_one problem h neighbours))
  have lower : 0 < box_count problem h
      (merge_along (merge (tuple_table problem h) first_pivot) pivots) neighbours := by
    unfold box_count
    rw [Finset.card_pos, Finset.filter_nonempty_iff]
    exact ((merge_along_represents_iff problem h pivots _ neighbours).trans
      ((merge_represents_iff problem h _ first_pivot neighbours).trans
        (tuple_table_represents_iff problem h neighbours current))).mpr compatible
  omega

def is_rule_four_step (problem reduced : bct) : Prop :=
  ∃ h table name, h ∈ problem.vertices ∧ h ∉ problem.originals ∧
    is_aaai_construction problem h table ∧ Set.InjOn name table ∧
      reduced = rule_four problem h table name

theorem rule_four_step_counts (problem reduced : bct) (step : is_rule_four_step problem reduced)
    (tuple : ℕ → ℕ) : extension_count reduced tuple ≤ extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  obtain ⟨h, table, name, h_vertex, h_hidden, construction, injective, rfl⟩ := step
  exact ⟨rule_four_count_le problem h h_vertex h_hidden table name injective tuple
    fun neighbours current => construction_count_le problem h table construction neighbours current,
    rule_four_relation problem h h_vertex h_hidden table name injective
      (construction_is_valid problem h table construction) tuple⟩

def is_any_step (problem reduced : bct) : Prop :=
  is_rule_one_step problem reduced ∨ is_rule_two_step problem reduced ∨
    is_rule_three_step problem reduced ∨ is_rule_four_step problem reduced

theorem any_step_counts (problem reduced : bct) (step : is_any_step problem reduced) (tuple : ℕ → ℕ) :
    extension_count reduced tuple ≤ extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  rcases step with one | two | three | four
  · exact rule_one_step_counts problem reduced one tuple
  · exact rule_two_step_counts problem reduced two tuple
  · exact ⟨(rule_three_step_counts problem reduced three tuple).1.le,
      (rule_three_step_counts problem reduced three tuple).2⟩
  · exact rule_four_step_counts problem reduced four tuple

theorem any_steps_counts (problem reduced : bct) (steps : Relation.ReflTransGen is_any_step problem reduced)
    (tuple : ℕ → ℕ) : extension_count reduced tuple ≤ extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  induction steps with
  | refl => exact ⟨le_rfl, Iff.rfl⟩
  | tail _ last hypothesis =>
    have counted := any_step_counts _ _ last tuple
    exact ⟨counted.1.trans hypothesis.1, counted.2.trans hypothesis.2⟩

theorem any_steps_keep_unique_extension (problem reduced : bct)
    (steps : Relation.ReflTransGen is_any_step problem reduced)
    (unique : has_unique_extension problem) : has_unique_extension reduced := by
  intro tuple relation
  have counted := any_steps_counts problem reduced steps tuple
  have positive := (extension_count_pos_iff reduced tuple).mpr relation
  have old := unique tuple (counted.2.mp relation)
  omega

def is_algorithm_one_run (problem reduced : bct) : Prop :=
  ∃ after_one after_two after_four after_two_again after_three after_four_again,
    Relation.ReflTransGen is_rule_one_step problem after_one ∧
    Relation.ReflTransGen is_rule_two_step after_one after_two ∧
    Relation.ReflTransGen is_rule_four_step after_two after_four ∧
    Relation.ReflTransGen is_rule_two_step after_four after_two_again ∧
    Relation.ReflTransGen is_rule_three_step after_two_again after_three ∧
    Relation.ReflTransGen is_rule_four_step after_three after_four_again ∧
    Relation.ReflTransGen is_rule_two_step after_four_again reduced

theorem algorithm_one_run_is_any_steps (problem reduced : bct) (run : is_algorithm_one_run problem reduced) :
    Relation.ReflTransGen is_any_step problem reduced := by
  obtain ⟨_, _, _, _, _, _, one, two, four, two_again, three, four_again, last⟩ := run
  have from_one := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inl step : is_any_step _ _)) _ _ one
  have from_two := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inr (Or.inl step) : is_any_step _ _)) _ _ two
  have from_four := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inr (Or.inr (Or.inr step)) : is_any_step _ _)) _ _ four
  have from_two_again := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inr (Or.inl step) : is_any_step _ _)) _ _ two_again
  have from_three := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inr (Or.inr (Or.inl step)) : is_any_step _ _)) _ _ three
  have from_four_again := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inr (Or.inr (Or.inr step)) : is_any_step _ _)) _ _ four_again
  have from_last := Relation.ReflTransGen.mono (p := is_any_step)
    (fun _ _ step => (Or.inr (Or.inl step) : is_any_step _ _)) _ _ last
  exact from_one.trans (from_two.trans (from_four.trans (from_two_again.trans
    (from_three.trans (from_four_again.trans from_last)))))

theorem algorithm_one_keeps_unique_extension (problem reduced : bct)
    (run : is_algorithm_one_run problem reduced) (unique : has_unique_extension problem) :
    has_unique_extension reduced :=
  any_steps_keep_unique_extension problem reduced (algorithm_one_run_is_any_steps problem reduced run)
    unique

end rules
end parsimony
