import parsimony.rules.minimal_support_under_rules

namespace parsimony
namespace rules

open scoped Classical

section grouping

variable (problem : bct) (order : List ℕ) (h pivot : ℕ) (name : Finset (ℕ × ℕ) → ℕ)

noncomputable def grouped_table : Finset (Finset (ℕ × ℕ)) :=
  merge (value_table problem h) pivot

noncomputable def group_of (a : ℕ) : Finset (ℕ × ℕ) :=
  merged_box (value_table problem h) pivot (value_box problem h a)

noncomputable def grouped_problem : bct :=
  rule_four problem h (grouped_table problem h pivot) name

theorem group_of_mem (a : ℕ) (a_mem : a ∈ problem.domain h) :
    group_of problem h pivot a ∈ grouped_table problem h pivot :=
  Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ a_mem)

theorem grouped_tree_order (tree : is_tree_order problem order) :
    is_tree_order (grouped_problem problem h pivot name) order := tree

theorem grouped_root (root : root_is_original problem order) :
    root_is_original (grouped_problem problem h pivot name) order := root

theorem grouped_relation_from (injective : Set.InjOn name (grouped_table problem h pivot)) (z b : ℕ)
    (z_ne_h : z ≠ h) (box : Finset (ℕ × ℕ)) (box_mem : box ∈ grouped_table problem h pivot) :
    (name box, b) ∈ (grouped_problem problem h pivot name).relation h z ↔ (z, b) ∈ box := by
  have side := box_side_member (grouped_table problem h pivot) name injective z box box_mem b
  simpa [grouped_problem, rule_four, z_ne_h] using side

theorem grouped_relation_other (u v : ℕ) (u_ne_h : u ≠ h) (v_ne_h : v ≠ h) :
    (grouped_problem problem h pivot name).relation u v = problem.relation u v := by
  simp [grouped_problem, rule_four, u_ne_h, v_ne_h]

noncomputable def grouped_back (selected : ℕ → Finset ℕ) : ℕ → Finset ℕ :=
  Function.update selected h ((problem.domain h).filter fun a =>
    name (group_of problem h pivot a) ∈ selected h ∧
      ∀ z, problem.edge h z → before order h z → ∃ b ∈ selected z, (a, b) ∈ problem.relation h z)

theorem class_member_fits (injective : Set.InjOn name (grouped_table problem h pivot)) (tuple : ℕ → ℕ)
    (selected : ℕ → Finset ℕ)
    (selection : is_selection (grouped_problem problem h pivot name) order tuple selected)
    (a0 : ℕ) (a0_mem : a0 ∈ problem.domain h)
    (group_selected : name (group_of problem h pivot a0) ∈ selected h)
    (a : ℕ) (a_mem : a ∈ problem.domain h)
    (agree : agree_outside pivot (value_box problem h a0) (value_box problem h a))
    (at_pivot : problem.edge h pivot → before order h pivot →
      ∃ b ∈ selected pivot, (a, b) ∈ problem.relation h pivot) :
    a ∈ grouped_back problem order h pivot name selected h ∧
      group_of problem h pivot a = group_of problem h pivot a0 := by
  have same_group : group_of problem h pivot a = group_of problem h pivot a0 :=
    (merged_box_congr (value_table problem h) pivot _ _ agree).symm
  refine ⟨?_, same_group⟩
  unfold grouped_back
  rw [Function.update_self, Finset.mem_filter]
  refine ⟨a_mem, same_group ▸ group_selected, fun z edge_h_z h_before => ?_⟩
  by_cases z_is_pivot : z = pivot
  · subst z_is_pivot
    exact at_pivot edge_h_z h_before
  · have z_ne_h : z ≠ h := (edge_ne problem h z edge_h_z).symm
    obtain ⟨b, b_selected, allowed⟩ := selection.2.2.2 h z edge_h_z h_before _ group_selected
    rw [grouped_relation_from problem h pivot name injective z b z_ne_h _
      (group_of_mem problem h pivot a0 a0_mem)] at allowed
    obtain ⟨other, _, other_agree, literal⟩ := (mem_merged_box _ pivot _ _).mp allowed
    have equivalence := agree_outside_equivalence pivot
    have to_a := equivalence.trans (equivalence.symm other_agree) agree
    have in_a := ((agree_outside_iff pivot other _).mp to_a (z, b) z_is_pivot).mp literal
    exact ⟨b, b_selected, ((mem_value_box problem h a z b).mp in_a).2⟩

theorem compatible_member (injective : Set.InjOn name (grouped_table problem h pivot)) (tuple : ℕ → ℕ)
    (selected : ℕ → Finset ℕ)
    (selection : is_selection (grouped_problem problem h pivot name) order tuple selected)
    (a0 : ℕ) (a0_mem : a0 ∈ problem.domain h)
    (group_selected : name (group_of problem h pivot a0) ∈ selected h) :
    ∃ a ∈ grouped_back problem order h pivot name selected h,
      group_of problem h pivot a = group_of problem h pivot a0 := by
  by_cases pivot_child : problem.edge h pivot ∧ before order h pivot
  · obtain ⟨edge_h_pivot, h_before⟩ := pivot_child
    have pivot_ne_h : pivot ≠ h := (edge_ne problem h pivot edge_h_pivot).symm
    obtain ⟨b, b_selected, allowed⟩ := selection.2.2.2 h pivot edge_h_pivot h_before _ group_selected
    rw [grouped_relation_from problem h pivot name injective pivot b pivot_ne_h _
      (group_of_mem problem h pivot a0 a0_mem)] at allowed
    obtain ⟨other, other_mem, other_agree, literal⟩ := (mem_merged_box _ pivot _ _).mp allowed
    obtain ⟨a, a_mem, rfl⟩ := Finset.mem_image.mp other_mem
    have fits := class_member_fits problem order h pivot name injective tuple selected selection a0 a0_mem
      group_selected a a_mem other_agree fun _ _ =>
        ⟨b, b_selected, ((mem_value_box problem h a pivot b).mp literal).2⟩
    exact ⟨a, fits.1, fits.2⟩
  · have fits := class_member_fits problem order h pivot name injective tuple selected selection a0 a0_mem
      group_selected a0 a0_mem ((agree_outside_equivalence pivot).refl _) fun edge_h_pivot h_before =>
        absurd ⟨edge_h_pivot, h_before⟩ pivot_child
    exact ⟨a0, fits.1, fits.2⟩

theorem compatible_member_with_literal (nodup : order.Nodup)
    (injective : Set.InjOn name (grouped_table problem h pivot))
    (tuple : ℕ → ℕ) (selected : ℕ → Finset ℕ)
    (selection : is_selection (grouped_problem problem h pivot name) order tuple selected)
    (a0 : ℕ) (a0_mem : a0 ∈ problem.domain h)
    (group_selected : name (group_of problem h pivot a0) ∈ selected h) (u c : ℕ)
    (u_before : before order u h) (literal_mem : (u, c) ∈ group_of problem h pivot a0) :
    ∃ a ∈ grouped_back problem order h pivot name selected h, (a, c) ∈ problem.relation h u := by
  have equivalence := agree_outside_equivalence pivot
  by_cases u_is_pivot : u = pivot
  · subst u_is_pivot
    obtain ⟨other, other_mem, other_agree, literal⟩ := (mem_merged_box _ u _ _).mp literal_mem
    obtain ⟨a, a_mem, rfl⟩ := Finset.mem_image.mp other_mem
    have fits := class_member_fits problem order h u name injective tuple selected selection a0 a0_mem
      group_selected a a_mem other_agree fun _ h_before =>
        absurd u_before (before_asymm order nodup _ _ h_before)
    exact ⟨a, fits.1, ((mem_value_box problem h a u c).mp literal).2⟩
  · obtain ⟨a, a_back, same_group⟩ := compatible_member problem order h pivot name injective tuple
      selected selection a0 a0_mem group_selected
    refine ⟨a, a_back, ?_⟩
    have in_group : (u, c) ∈ group_of problem h pivot a := same_group ▸ literal_mem
    obtain ⟨other, _, other_agree, literal⟩ := (mem_merged_box _ pivot _ _).mp in_group
    have in_a := ((agree_outside_iff pivot _ other).mp other_agree (u, c) u_is_pivot).mpr literal
    exact ((mem_value_box problem h a u c).mp in_a).2

theorem grouped_back_is_selection (nodup : order.Nodup) (h_hidden : h ∉ problem.originals)
    (injective : Set.InjOn name (grouped_table problem h pivot)) (tuple : ℕ → ℕ)
    (selected : ℕ → Finset ℕ)
    (selection : is_selection (grouped_problem problem h pivot name) order tuple selected) :
    is_selection problem order tuple (grouped_back problem order h pivot name selected) := by
  have off_h : ∀ x, x ≠ h → grouped_back problem order h pivot name selected x = selected x :=
    fun x x_ne => Function.update_of_ne x_ne _ _
  obtain ⟨inside, outside, at_originals, supported⟩ := selection
  refine ⟨fun x x_vertex => ?_, fun x x_out => ?_, fun x x_original => ?_,
    fun u v edge_u_v u_before c c_selected => ?_⟩
  · by_cases x_is_h : x = h
    · subst x_is_h
      unfold grouped_back
      rw [Function.update_self]
      exact Finset.filter_subset _ _
    · rw [off_h x x_is_h]
      have stated := inside x x_vertex
      simpa [grouped_problem, rule_four, x_is_h] using stated
  · by_cases x_is_h : x = h
    · subst x_is_h
      unfold grouped_back
      rw [Function.update_self]
      refine Finset.filter_eq_empty_iff.mpr fun a _ both => ?_
      have none : selected x = ∅ := outside x x_out
      rw [none] at both
      exact absurd both.1 (Finset.notMem_empty _)
    · rw [off_h x x_is_h]
      exact outside x x_out
  · rw [off_h x (original_ne_hidden h_hidden x_original)]
    exact at_originals x x_original
  · by_cases u_is_h : u = h
    · subst u_is_h
      have v_ne_u : v ≠ u := (edge_ne problem u v edge_u_v).symm
      rw [off_h v v_ne_u]
      unfold grouped_back at c_selected
      rw [Function.update_self, Finset.mem_filter] at c_selected
      exact c_selected.2.2 v edge_u_v u_before
    · rw [off_h u u_is_h] at c_selected
      by_cases v_is_h : v = h
      · subst v_is_h
        obtain ⟨g, g_selected, allowed⟩ := supported u v edge_u_v u_before c c_selected
        have v_vertex := edge_vertices_right problem u v edge_u_v
        have g_domain := inside v v_vertex g_selected
        simp only [grouped_problem, rule_four, ite_true, Finset.mem_image] at g_domain
        obtain ⟨box, box_mem, rfl⟩ := g_domain
        have swapped := ((grouped_problem problem v pivot name).relation_symm _ _ _ _).mp allowed
        rw [grouped_relation_from problem v pivot name injective u c u_is_h box box_mem] at swapped
        obtain ⟨inner, inner_mem, rfl⟩ := Finset.mem_image.mp box_mem
        obtain ⟨a0, a0_mem, rfl⟩ := Finset.mem_image.mp inner_mem
        obtain ⟨a, a_back, a_allowed⟩ := compatible_member_with_literal problem order v pivot name nodup
          injective tuple selected ⟨inside, outside, at_originals, supported⟩ a0 a0_mem g_selected u c
          u_before swapped
        exact ⟨a, a_back, (problem.relation_symm _ _ _ _).mp a_allowed⟩
      · rw [off_h v v_is_h]
        have stated := supported u v edge_u_v u_before c c_selected
        rw [grouped_relation_other problem h pivot name u v u_is_h v_is_h] at stated
        exact stated

theorem grouped_back_injective (h_vertex : h ∈ problem.vertices)
    (injective : Set.InjOn name (grouped_table problem h pivot)) (tuple : ℕ → ℕ) :
    Set.InjOn (grouped_back problem order h pivot name)
      (selections (grouped_problem problem h pivot name) order tuple) := by
  have recovered : ∀ selected ∈ selections (grouped_problem problem h pivot name) order tuple,
      ∀ g, g ∈ selected h ↔ ∃ a ∈ grouped_back problem order h pivot name selected h,
        name (group_of problem h pivot a) = g := by
    intro selected selection g
    constructor
    · intro g_selected
      have g_domain := selection.1 h h_vertex g_selected
      simp only [grouped_problem, rule_four, ite_true, Finset.mem_image] at g_domain
      obtain ⟨box, box_mem, rfl⟩ := g_domain
      obtain ⟨inner, inner_mem, rfl⟩ := Finset.mem_image.mp box_mem
      obtain ⟨a0, a0_mem, rfl⟩ := Finset.mem_image.mp inner_mem
      obtain ⟨a, a_back, same_group⟩ := compatible_member problem order h pivot name injective tuple
        selected selection a0 a0_mem g_selected
      exact ⟨a, a_back, by rw [same_group]; rfl⟩
    · rintro ⟨a, a_back, rfl⟩
      unfold grouped_back at a_back
      rw [Function.update_self, Finset.mem_filter] at a_back
      exact a_back.2.1
  intro first first_mem second second_mem same
  funext x
  by_cases x_is_h : x = h
  · subst x_is_h
    ext g
    rw [recovered first first_mem g, recovered second second_mem g, same]
  · have at_x := congrFun same x
    unfold grouped_back at at_x
    rwa [Function.update_of_ne x_is_h, Function.update_of_ne x_is_h] at at_x

theorem grouping_minimal_support_count_le (tree : is_tree_order problem order)
    (h_vertex : h ∈ problem.vertices) (h_hidden : h ∉ problem.originals)
    (injective : Set.InjOn name (grouped_table problem h pivot)) (listing grouped_listing : ℕ → List ℕ)
    (is_listing_old : is_listing problem listing)
    (is_listing_new : is_listing (grouped_problem problem h pivot name) grouped_listing)
    (old_nonempty : ∀ x ∈ problem.originals, (problem.domain x).Nonempty) (tuple : ℕ → ℕ) :
    (minimal_support_models_over (grouped_problem problem h pivot name) grouped_listing order tuple).ncard
      ≤ (minimal_support_models_over problem listing order tuple).ncard := by
  have new_nonempty : ∀ x ∈ (grouped_problem problem h pivot name).originals,
      ((grouped_problem problem h pivot name).domain x).Nonempty := by
    intro x x_original
    have x_ne_h := original_ne_hidden h_hidden x_original
    have stated := old_nonempty x x_original
    simpa [grouped_problem, rule_four, x_ne_h] using stated
  rw [minimal_support_count_eq_selections _ grouped_listing is_listing_new new_nonempty,
    minimal_support_count_eq_selections problem listing is_listing_old old_nonempty]
  exact Set.ncard_le_ncard_of_injOn (grouped_back problem order h pivot name)
    (fun selected selection => grouped_back_is_selection problem order h pivot name tree.1 h_hidden
      injective tuple selected selection)
    (grouped_back_injective problem order h pivot name h_vertex injective tuple)
    (selections_finite problem order tuple)

end grouping

end rules
end parsimony
