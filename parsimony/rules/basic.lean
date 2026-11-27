import Mathlib

namespace parsimony
namespace rules

open scoped Classical

structure bct where
  vertices : Finset ℕ
  originals : Finset ℕ
  originals_subset : originals ⊆ vertices
  domain : ℕ → Finset ℕ
  edge : ℕ → ℕ → Prop
  edge_symm : ∀ x y, edge x y → edge y x
  edge_irrefl : ∀ x, ¬ edge x x
  edge_vertices : ∀ x y, edge x y → x ∈ vertices
  relation : ℕ → ℕ → Finset (ℕ × ℕ)
  relation_symm : ∀ x y a b, (a, b) ∈ relation x y ↔ (b, a) ∈ relation y x

def is_solution (problem : bct) (candidate : ℕ → ℕ) : Prop :=
  (∀ x ∈ problem.vertices, candidate x ∈ problem.domain x) ∧
  (∀ x, x ∉ problem.vertices → candidate x = 0) ∧
  ∀ x y, problem.edge x y → (candidate x, candidate y) ∈ problem.relation x y

def extensions (problem : bct) (tuple : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {candidate | is_solution problem candidate ∧ ∀ x ∈ problem.originals, candidate x = tuple x}

noncomputable def extension_count (problem : bct) (tuple : ℕ → ℕ) : ℕ :=
  (extensions problem tuple).ncard

def in_relation (problem : bct) (tuple : ℕ → ℕ) : Prop :=
  (extensions problem tuple).Nonempty

def has_unique_extension (problem : bct) : Prop :=
  ∀ tuple, in_relation problem tuple → extension_count problem tuple = 1

theorem edge_vertices_right (problem : bct) (x y : ℕ) (edge_x_y : problem.edge x y) :
    y ∈ problem.vertices :=
  problem.edge_vertices y x (problem.edge_symm x y edge_x_y)

theorem edge_ne (problem : bct) (x y : ℕ) (edge_x_y : problem.edge x y) : x ≠ y := by
  intro x_is_y
  rw [x_is_y] at edge_x_y
  exact problem.edge_irrefl y edge_x_y

theorem bounded_functions_finite (vertices : Finset ℕ) (domain : ℕ → Finset ℕ) :
    {candidate : ℕ → ℕ | (∀ x ∈ vertices, candidate x ∈ domain x) ∧
      ∀ x, x ∉ vertices → candidate x = 0}.Finite := by
  refine Set.Finite.subset (Set.finite_range
    (fun values : ((x : {x // x ∈ vertices}) → {a // a ∈ domain x.val}) =>
      fun x : ℕ => if x_mem : x ∈ vertices then (values ⟨x, x_mem⟩).val else 0)) ?_
  rintro candidate ⟨inside, outside⟩
  refine ⟨fun x => ⟨candidate x.val, inside x.val x.property⟩, ?_⟩
  funext x
  by_cases x_mem : x ∈ vertices
  · simp [x_mem]
  · simp [x_mem, outside x x_mem]

theorem extensions_finite (problem : bct) (tuple : ℕ → ℕ) : (extensions problem tuple).Finite :=
  (bounded_functions_finite problem.vertices problem.domain).subset
    fun _ member => ⟨member.1.1, member.1.2.1⟩

theorem extension_count_pos_iff (problem : bct) (tuple : ℕ → ℕ) :
    0 < extension_count problem tuple ↔ in_relation problem tuple :=
  Set.ncard_pos (extensions_finite problem tuple)

theorem original_ne_hidden {problem : bct} {h : ℕ} (h_hidden : h ∉ problem.originals) {x : ℕ}
    (x_original : x ∈ problem.originals) : x ≠ h := by
  rintro rfl
  exact h_hidden x_original

def rule_one (problem : bct) (h y : ℕ) (h_hidden : h ∉ problem.originals) : bct where
  vertices := problem.vertices.erase h
  originals := problem.originals
  originals_subset := fun _ x_original =>
    Finset.mem_erase.mpr ⟨original_ne_hidden h_hidden x_original, problem.originals_subset x_original⟩
  domain := fun x => if x = y then
    (problem.domain y).filter fun b => ∃ a ∈ problem.domain h, (b, a) ∈ problem.relation y h
    else problem.domain x
  edge := fun u v => u ≠ h ∧ v ≠ h ∧ problem.edge u v
  edge_symm := fun _ _ both => ⟨both.2.1, both.1, problem.edge_symm _ _ both.2.2⟩
  edge_irrefl := fun x both => problem.edge_irrefl x both.2.2
  edge_vertices := fun _ _ both =>
    Finset.mem_erase.mpr ⟨both.1, problem.edge_vertices _ _ both.2.2⟩
  relation := problem.relation
  relation_symm := problem.relation_symm

def is_rule_one_step (problem reduced : bct) : Prop :=
  ∃ h y, ∃ h_hidden : h ∉ problem.originals, problem.edge h y ∧
    (∀ z, problem.edge h z → z = y) ∧ reduced = rule_one problem h y h_hidden

theorem rule_one_extensions (problem : bct) (h y : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (only_neighbour : ∀ z, problem.edge h z → z = y)
    (tuple : ℕ → ℕ) :
    extensions (rule_one problem h y h_hidden) tuple =
      (fun candidate => Function.update candidate h 0) '' extensions problem tuple := by
  have y_ne_h : y ≠ h := (edge_ne problem h y edge_h_y).symm
  have y_vertex : y ∈ problem.vertices := edge_vertices_right problem h y edge_h_y
  have h_vertex : h ∈ problem.vertices := problem.edge_vertices h y edge_h_y
  ext reduced_candidate
  constructor
  · rintro ⟨⟨inside, outside, holds⟩, agrees⟩
    have at_y := inside y (Finset.mem_erase.mpr ⟨y_ne_h, y_vertex⟩)
    simp only [rule_one, ite_true, Finset.mem_filter] at at_y
    obtain ⟨at_y_old, a, a_mem, a_allowed⟩ := at_y
    have at_h : reduced_candidate h = 0 := outside h (by simp [rule_one])
    refine ⟨Function.update reduced_candidate h a, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro x x_vertex
      by_cases x_is_h : x = h
      · subst x_is_h
        simpa using a_mem
      · rw [Function.update_of_ne x_is_h]
        have x_in := inside x (Finset.mem_erase.mpr ⟨x_is_h, x_vertex⟩)
        by_cases x_is_y : x = y
        · subst x_is_y
          exact at_y_old
        · simpa [rule_one, x_is_y] using x_in
    · intro x x_out
      have x_ne_h : x ≠ h := fun x_is_h => x_out (x_is_h ▸ h_vertex)
      rw [Function.update_of_ne x_ne_h]
      exact outside x (by simp [rule_one, x_out])
    · intro u v edge_u_v
      by_cases u_is_h : u = h
      · subst u_is_h
        have v_is_y := only_neighbour v edge_u_v
        subst v_is_y
        rw [Function.update_self, Function.update_of_ne y_ne_h]
        exact (problem.relation_symm _ _ _ _).mpr a_allowed
      · by_cases v_is_h : v = h
        · subst v_is_h
          have u_is_y := only_neighbour u (problem.edge_symm _ _ edge_u_v)
          subst u_is_y
          rw [Function.update_self, Function.update_of_ne y_ne_h]
          exact a_allowed
        · rw [Function.update_of_ne u_is_h, Function.update_of_ne v_is_h]
          exact holds u v ⟨u_is_h, v_is_h, edge_u_v⟩
    · intro x x_original
      rw [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact agrees x x_original
    · funext x
      by_cases x_is_h : x = h
      · subst x_is_h
        simp [at_h]
      · simp [Function.update_of_ne x_is_h]
  · rintro ⟨candidate, ⟨⟨inside, outside, holds⟩, agrees⟩, rfl⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x x_vertex
      obtain ⟨x_ne_h, x_old⟩ := Finset.mem_erase.mp x_vertex
      simp only [Function.update_of_ne x_ne_h]
      by_cases x_is_y : x = y
      · subst x_is_y
        simp only [rule_one, ite_true, Finset.mem_filter]
        exact ⟨inside x x_old, candidate h, inside h h_vertex,
          holds x h (problem.edge_symm _ _ edge_h_y)⟩
      · simpa [rule_one, x_is_y] using inside x x_old
    · intro x x_out
      by_cases x_is_h : x = h
      · subst x_is_h
        simp
      · simp only [Function.update_of_ne x_is_h]
        exact outside x fun x_old => x_out (Finset.mem_erase.mpr ⟨x_is_h, x_old⟩)
    · rintro u v ⟨u_ne_h, v_ne_h, edge_u_v⟩
      simp only [Function.update_of_ne u_ne_h, Function.update_of_ne v_ne_h]
      exact holds u v edge_u_v
    · intro x x_original
      simp only [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact agrees x x_original

noncomputable def joined_pairs (problem : bct) (h y z : ℕ) : Finset (ℕ × ℕ) :=
  (problem.domain y ×ˢ problem.domain z).filter fun pair =>
    (∃ a ∈ problem.domain h, (pair.1, a) ∈ problem.relation y h ∧ (a, pair.2) ∈ problem.relation h z) ∧
      (problem.edge y z → pair ∈ problem.relation y z)

theorem joined_pairs_symm (problem : bct) (h y z a b : ℕ) :
    (a, b) ∈ joined_pairs problem h y z ↔ (b, a) ∈ joined_pairs problem h z y := by
  simp only [joined_pairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨a_mem, b_mem⟩, ⟨c, c_mem, first, second⟩, old⟩
    exact ⟨⟨b_mem, a_mem⟩, ⟨c, c_mem, (problem.relation_symm _ _ _ _).mp second,
      (problem.relation_symm _ _ _ _).mp first⟩, fun edge_z_y =>
      (problem.relation_symm _ _ _ _).mp (old (problem.edge_symm _ _ edge_z_y))⟩
  · rintro ⟨⟨b_mem, a_mem⟩, ⟨c, c_mem, first, second⟩, old⟩
    exact ⟨⟨a_mem, b_mem⟩, ⟨c, c_mem, (problem.relation_symm _ _ _ _).mp second,
      (problem.relation_symm _ _ _ _).mp first⟩, fun edge_y_z =>
      (problem.relation_symm _ _ _ _).mp (old (problem.edge_symm _ _ edge_y_z))⟩

noncomputable def rule_two (problem : bct) (h y z : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (edge_h_z : problem.edge h z) (y_ne_z : y ≠ z) : bct where
  vertices := problem.vertices.erase h
  originals := problem.originals
  originals_subset := fun _ x_original =>
    Finset.mem_erase.mpr ⟨original_ne_hidden h_hidden x_original, problem.originals_subset x_original⟩
  domain := problem.domain
  edge := fun u v => (u ≠ h ∧ v ≠ h ∧ problem.edge u v) ∨ (u = y ∧ v = z) ∨ (u = z ∧ v = y)
  edge_symm := by
    rintro u v (⟨u_ne, v_ne, edge_u_v⟩ | both | both)
    · exact Or.inl ⟨v_ne, u_ne, problem.edge_symm _ _ edge_u_v⟩
    · exact Or.inr (Or.inr ⟨both.2, both.1⟩)
    · exact Or.inr (Or.inl ⟨both.2, both.1⟩)
  edge_irrefl := by
    rintro x (⟨_, _, edge_x_x⟩ | both | both)
    · exact problem.edge_irrefl x edge_x_x
    · exact y_ne_z (both.1.symm.trans both.2)
    · exact y_ne_z (both.2.symm.trans both.1)
  edge_vertices := by
    rintro u v (⟨u_ne, _, edge_u_v⟩ | both | both)
    · exact Finset.mem_erase.mpr ⟨u_ne, problem.edge_vertices _ _ edge_u_v⟩
    · rw [both.1]
      exact Finset.mem_erase.mpr ⟨(edge_ne problem h y edge_h_y).symm,
        edge_vertices_right problem h y edge_h_y⟩
    · rw [both.1]
      exact Finset.mem_erase.mpr ⟨(edge_ne problem h z edge_h_z).symm,
        edge_vertices_right problem h z edge_h_z⟩
  relation := fun u v => if u = y ∧ v = z then joined_pairs problem h y z
    else if u = z ∧ v = y then joined_pairs problem h z y else problem.relation u v
  relation_symm := by
    intro u v a b
    by_cases first : u = y ∧ v = z
    · obtain ⟨rfl, rfl⟩ := first
      have not_back : ¬ (v = u ∧ u = v) := fun both => y_ne_z both.2
      simp only [and_self, ite_true, not_back, ite_false]
      exact joined_pairs_symm problem h u v a b
    · by_cases second : u = z ∧ v = y
      · obtain ⟨rfl, rfl⟩ := second
        simp only [first, and_self, ite_true, ite_false]
        exact joined_pairs_symm problem h u v a b
      · have first_back : ¬ (v = y ∧ u = z) := fun both => second ⟨both.2, both.1⟩
        have second_back : ¬ (v = z ∧ u = y) := fun both => first ⟨both.2, both.1⟩
        simp only [first, second, first_back, second_back, ite_false]
        exact problem.relation_symm u v a b

def is_rule_two_step (problem reduced : bct) : Prop :=
  ∃ h y z, ∃ h_hidden : h ∉ problem.originals, ∃ edge_h_y : problem.edge h y,
    ∃ edge_h_z : problem.edge h z, ∃ y_ne_z : y ≠ z,
      (∀ w, problem.edge h w → w = y ∨ w = z) ∧
        reduced = rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z

theorem rule_two_extensions (problem : bct) (h y z : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (edge_h_z : problem.edge h z) (y_ne_z : y ≠ z)
    (two_neighbours : ∀ w, problem.edge h w → w = y ∨ w = z) (tuple : ℕ → ℕ) :
    extensions (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z) tuple =
      (fun candidate => Function.update candidate h 0) '' extensions problem tuple := by
  have y_ne_h : y ≠ h := (edge_ne problem h y edge_h_y).symm
  have z_ne_h : z ≠ h := (edge_ne problem h z edge_h_z).symm
  have y_vertex : y ∈ problem.vertices := edge_vertices_right problem h y edge_h_y
  have z_vertex : z ∈ problem.vertices := edge_vertices_right problem h z edge_h_z
  have h_vertex : h ∈ problem.vertices := problem.edge_vertices h y edge_h_y
  ext reduced_candidate
  constructor
  · rintro ⟨⟨inside, outside, holds⟩, agrees⟩
    have joined := holds y z (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simp only [rule_two, and_self, ite_true, joined_pairs, Finset.mem_filter, Finset.mem_product] at joined
    obtain ⟨⟨_, _⟩, ⟨a, a_mem, first_allowed, second_allowed⟩, old_allowed⟩ := joined
    have at_h : reduced_candidate h = 0 := outside h (by simp [rule_two])
    have kept : ∀ u v, u ≠ h → v ≠ h → problem.edge u v →
        (reduced_candidate u, reduced_candidate v) ∈ problem.relation u v := by
      intro u v u_ne v_ne edge_u_v
      by_cases first : u = y ∧ v = z
      · obtain ⟨rfl, rfl⟩ := first
        exact old_allowed edge_u_v
      · by_cases second : u = z ∧ v = y
        · obtain ⟨rfl, rfl⟩ := second
          exact (problem.relation_symm _ _ _ _).mp (old_allowed (problem.edge_symm _ _ edge_u_v))
        · have stated := holds u v (Or.inl ⟨u_ne, v_ne, edge_u_v⟩)
          simpa [rule_two, first, second] using stated
    refine ⟨Function.update reduced_candidate h a, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro x x_vertex
      by_cases x_is_h : x = h
      · subst x_is_h
        simpa using a_mem
      · rw [Function.update_of_ne x_is_h]
        exact inside x (Finset.mem_erase.mpr ⟨x_is_h, x_vertex⟩)
    · intro x x_out
      have x_ne_h : x ≠ h := fun x_is_h => x_out (x_is_h ▸ h_vertex)
      rw [Function.update_of_ne x_ne_h]
      exact outside x (by simp [rule_two, x_out])
    · intro u v edge_u_v
      by_cases u_is_h : u = h
      · subst u_is_h
        rcases two_neighbours v edge_u_v with rfl | rfl
        · rw [Function.update_self, Function.update_of_ne y_ne_h]
          exact (problem.relation_symm _ _ _ _).mpr first_allowed
        · rw [Function.update_self, Function.update_of_ne z_ne_h]
          exact second_allowed
      · by_cases v_is_h : v = h
        · subst v_is_h
          rcases two_neighbours u (problem.edge_symm _ _ edge_u_v) with rfl | rfl
          · rw [Function.update_self, Function.update_of_ne y_ne_h]
            exact first_allowed
          · rw [Function.update_self, Function.update_of_ne z_ne_h]
            exact (problem.relation_symm _ _ _ _).mpr second_allowed
        · rw [Function.update_of_ne u_is_h, Function.update_of_ne v_is_h]
          exact kept u v u_is_h v_is_h edge_u_v
    · intro x x_original
      rw [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact agrees x x_original
    · funext x
      by_cases x_is_h : x = h
      · subst x_is_h
        simp [at_h]
      · simp [Function.update_of_ne x_is_h]
  · rintro ⟨candidate, ⟨⟨inside, outside, holds⟩, agrees⟩, rfl⟩
    have y_h_allowed := holds y h (problem.edge_symm _ _ edge_h_y)
    have h_z_allowed := holds h z edge_h_z
    have y_z_joined : (candidate y, candidate z) ∈ joined_pairs problem h y z := by
      simp only [joined_pairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨inside y y_vertex, inside z z_vertex⟩,
        ⟨candidate h, inside h h_vertex, y_h_allowed, h_z_allowed⟩, fun edge_y_z => holds y z edge_y_z⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x x_vertex
      obtain ⟨x_ne_h, x_old⟩ := Finset.mem_erase.mp x_vertex
      simp only [Function.update_of_ne x_ne_h]
      exact inside x x_old
    · intro x x_out
      by_cases x_is_h : x = h
      · subst x_is_h
        simp
      · simp only [Function.update_of_ne x_is_h]
        exact outside x fun x_old => x_out (Finset.mem_erase.mpr ⟨x_is_h, x_old⟩)
    · intro u v edge_u_v
      have u_ne : u ≠ h := by
        rcases edge_u_v with both | both | both
        · exact both.1
        · exact both.1 ▸ y_ne_h
        · exact both.1 ▸ z_ne_h
      have v_ne : v ≠ h := by
        rcases edge_u_v with both | both | both
        · exact both.2.1
        · exact both.2 ▸ z_ne_h
        · exact both.2 ▸ y_ne_h
      simp only [Function.update_of_ne u_ne, Function.update_of_ne v_ne]
      by_cases first : u = y ∧ v = z
      · obtain ⟨rfl, rfl⟩ := first
        simpa [rule_two] using y_z_joined
      · by_cases second : u = z ∧ v = y
        · obtain ⟨rfl, rfl⟩ := second
          simp only [rule_two, first, and_self, ite_true, ite_false]
          exact (joined_pairs_symm problem h _ _ _ _).mp y_z_joined
        · simp only [rule_two, first, second, ite_false]
          rcases edge_u_v with both | both | both
          · exact holds u v both.2.2
          · exact absurd both first
          · exact absurd both second
    · intro x x_original
      simp only [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact agrees x x_original

theorem image_count_le (problem reduced : bct) (tuple : ℕ → ℕ) (forget : (ℕ → ℕ) → ℕ → ℕ)
    (image : extensions reduced tuple = forget '' extensions problem tuple) :
    extension_count reduced tuple ≤ extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  constructor
  · unfold extension_count
    rw [image]
    exact Set.ncard_image_le (extensions_finite problem tuple)
  · unfold in_relation
    rw [image]
    exact Set.image_nonempty

theorem rule_one_step_counts (problem reduced : bct) (step : is_rule_one_step problem reduced)
    (tuple : ℕ → ℕ) : extension_count reduced tuple ≤ extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  obtain ⟨h, y, h_hidden, edge_h_y, only_neighbour, rfl⟩ := step
  exact image_count_le _ _ _ _ (rule_one_extensions problem h y h_hidden edge_h_y only_neighbour tuple)

theorem rule_two_step_counts (problem reduced : bct) (step : is_rule_two_step problem reduced)
    (tuple : ℕ → ℕ) : extension_count reduced tuple ≤ extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  obtain ⟨h, y, z, h_hidden, edge_h_y, edge_h_z, y_ne_z, two_neighbours, rfl⟩ := step
  exact image_count_le _ _ _ _
    (rule_two_extensions problem h y z h_hidden edge_h_y edge_h_z y_ne_z two_neighbours tuple)

theorem rule_one_empty_domain (problem : bct) (h y : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (empty : (rule_one problem h y h_hidden).domain y = ∅)
    (candidate : ℕ → ℕ) : ¬ is_solution problem candidate := by
  rintro ⟨inside, _, holds⟩
  have member : candidate y ∈ (rule_one problem h y h_hidden).domain y := by
    simp only [rule_one, ite_true, Finset.mem_filter]
    exact ⟨inside y (edge_vertices_right problem h y edge_h_y), candidate h,
      inside h (problem.edge_vertices h y edge_h_y), holds y h (problem.edge_symm _ _ edge_h_y)⟩
  rw [empty] at member
  exact absurd member (Finset.notMem_empty _)

end rules
end parsimony
