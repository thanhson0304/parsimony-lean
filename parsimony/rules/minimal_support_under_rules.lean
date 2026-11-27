import parsimony.rules.minimal_support_reduced

namespace parsimony
namespace rules

open scoped Classical

theorem mem_order_iff (problem : bct) (order : List ℕ) (tree : is_tree_order problem order) (x : ℕ) :
    x ∈ order ↔ x ∈ problem.vertices := by
  rw [← tree.2.1, List.mem_toFinset]

theorem hidden_not_head (problem : bct) (order : List ℕ) (root : root_is_original problem order) (h : ℕ)
    (h_hidden : h ∉ problem.originals) : order.head? ≠ some h := by
  obtain ⟨first, at_head, first_original⟩ := root
  intro same
  rw [at_head, Option.some.injEq] at same
  exact h_hidden (same ▸ first_original)

theorem hidden_parent (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) :
    ∃! earlier, problem.edge earlier h ∧ before order earlier h :=
  tree.2.2 h ((mem_order_iff problem order tree h).mpr h_vertex)
    (hidden_not_head problem order root h h_hidden)

theorem before_ne (order : List ℕ) (nodup : order.Nodup) (x y : ℕ) (x_before : before order x y) :
    x ≠ y := by
  rintro rfl
  exact before_asymm order nodup x x x_before x_before

theorem erase_head (order : List ℕ) (h : ℕ) (not_head : order.head? ≠ some h) :
    (order.erase h).head? = order.head? := by
  cases order with
  | nil => rfl
  | cons first rest =>
    have first_ne : first ≠ h := by
      intro same
      exact not_head (by simp [same])
    rw [List.erase_cons_tail (by simpa using first_ne)]
    rfl

theorem erase_root_is_original (problem reduced : bct) (order : List ℕ) (h : ℕ)
    (root : root_is_original problem order) (h_hidden : h ∉ problem.originals)
    (same_originals : reduced.originals = problem.originals) :
    root_is_original reduced (order.erase h) := by
  obtain ⟨first, at_head, first_original⟩ := root
  refine ⟨first, ?_, same_originals ▸ first_original⟩
  rw [erase_head order h (hidden_not_head problem order ⟨first, at_head, first_original⟩ h h_hidden)]
  exact at_head

theorem erase_toFinset (order : List ℕ) (nodup : order.Nodup) (h : ℕ) :
    (order.erase h).toFinset = order.toFinset.erase h := by
  ext x
  rw [List.mem_toFinset, Finset.mem_erase, List.mem_toFinset, nodup.mem_erase_iff]

theorem leaf_parent_before (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (h y : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (only_neighbour : ∀ z, problem.edge h z → z = y) :
    before order y h := by
  obtain ⟨earlier, ⟨edge_earlier, earlier_before⟩, _⟩ := hidden_parent problem order tree root h
    (problem.edge_vertices h y edge_h_y) h_hidden
  rw [only_neighbour earlier (problem.edge_symm _ _ edge_earlier)] at earlier_before
  exact earlier_before

theorem rule_one_tree_order (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (h y : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (only_neighbour : ∀ z, problem.edge h z → z = y) :
    is_tree_order (rule_one problem h y h_hidden) (order.erase h) := by
  have y_before := leaf_parent_before problem order tree root h y h_hidden edge_h_y only_neighbour
  refine ⟨tree.1.erase h, ?_, fun later later_mem not_head => ?_⟩
  · rw [erase_toFinset order tree.1 h, tree.2.1]
    rfl
  · obtain ⟨later_ne, later_old⟩ := tree.1.mem_erase_iff.mp later_mem
    rw [erase_head order h (hidden_not_head problem order root h h_hidden)] at not_head
    obtain ⟨earlier, ⟨edge_earlier, earlier_before⟩, only⟩ := tree.2.2 later later_old not_head
    have earlier_ne : earlier ≠ h := by
      rintro rfl
      rw [only_neighbour later edge_earlier] at earlier_before
      exact before_asymm order tree.1 _ _ earlier_before y_before
    refine ⟨earlier, ⟨⟨earlier_ne, later_ne, edge_earlier⟩,
      (before_erase_iff order tree.1 h earlier later earlier_ne later_ne).mpr earlier_before⟩, ?_⟩
    rintro other ⟨⟨other_ne, _, edge_other⟩, other_before⟩
    exact only other ⟨edge_other,
      (before_erase_iff order tree.1 h other later other_ne later_ne).mp other_before⟩

theorem rule_one_selections (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (h y : ℕ) (h_hidden : h ∉ problem.originals)
    (edge_h_y : problem.edge h y) (only_neighbour : ∀ z, problem.edge h z → z = y) (tuple : ℕ → ℕ) :
    selections (rule_one problem h y h_hidden) (order.erase h) tuple =
      (fun selected => Function.update selected h ∅) '' selections problem order tuple := by
  have y_before := leaf_parent_before problem order tree root h y h_hidden edge_h_y only_neighbour
  have y_ne_h : y ≠ h := (edge_ne problem h y edge_h_y).symm
  have h_vertex : h ∈ problem.vertices := problem.edge_vertices h y edge_h_y
  ext reduced_selected
  constructor
  · rintro ⟨inside, outside, at_originals, supported⟩
    have at_h : reduced_selected h = ∅ := outside h (by simp [rule_one])
    have inside_y := inside y (Finset.mem_erase.mpr ⟨y_ne_h, edge_vertices_right problem h y edge_h_y⟩)
    simp only [rule_one, ite_true] at inside_y
    refine ⟨Function.update reduced_selected h (problem.domain h), ⟨fun x x_vertex => ?_,
      fun x x_out => ?_, fun x x_original => ?_, fun u v edge_u_v u_before a a_selected => ?_⟩, ?_⟩
    · by_cases x_is_h : x = h
      · subst x_is_h
        rw [Function.update_self]
      · rw [Function.update_of_ne x_is_h]
        have stated := inside x (Finset.mem_erase.mpr ⟨x_is_h, x_vertex⟩)
        by_cases x_is_y : x = y
        · subst x_is_y
          exact inside_y.trans (Finset.filter_subset _ _)
        · simpa [rule_one, x_is_y] using stated
    · have x_ne_h : x ≠ h := fun same => x_out (same ▸ h_vertex)
      rw [Function.update_of_ne x_ne_h]
      exact outside x fun member => x_out (Finset.mem_of_mem_erase member)
    · rw [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact at_originals x x_original
    · by_cases u_is_h : u = h
      · subst u_is_h
        rw [only_neighbour v edge_u_v] at u_before
        exact absurd y_before (before_asymm order tree.1 _ _ u_before)
      · rw [Function.update_of_ne u_is_h] at a_selected
        by_cases v_is_h : v = h
        · subst v_is_h
          have u_is_y := only_neighbour u (problem.edge_symm _ _ edge_u_v)
          subst u_is_y
          rw [Function.update_self]
          obtain ⟨_, b, b_mem, allowed⟩ := Finset.mem_filter.mp (inside_y a_selected)
          exact ⟨b, b_mem, allowed⟩
        · rw [Function.update_of_ne v_is_h]
          exact supported u v ⟨u_is_h, v_is_h, edge_u_v⟩
            ((before_erase_iff order tree.1 h u v u_is_h v_is_h).mpr u_before) a a_selected
    · funext x
      by_cases x_is_h : x = h
      · subst x_is_h
        simp [at_h]
      · simp [Function.update_of_ne x_is_h]
  · rintro ⟨selected, ⟨inside, outside, at_originals, supported⟩, rfl⟩
    refine ⟨fun x x_vertex => ?_, fun x x_out => ?_, fun x x_original => ?_,
      fun u v new_edge u_before a a_selected => ?_⟩
    · obtain ⟨x_ne_h, x_old⟩ := Finset.mem_erase.mp x_vertex
      simp only [Function.update_of_ne x_ne_h]
      by_cases x_is_y : x = y
      · subst x_is_y
        simp only [rule_one, ite_true]
        intro b b_selected
        obtain ⟨a, a_selected, allowed⟩ := supported x h (problem.edge_symm _ _ edge_h_y) y_before b
          b_selected
        exact Finset.mem_filter.mpr ⟨inside x x_old b_selected, a, inside h h_vertex a_selected, allowed⟩
      · simpa [rule_one, x_is_y] using inside x x_old
    · by_cases x_is_h : x = h
      · subst x_is_h
        simp
      · simp only [Function.update_of_ne x_is_h]
        exact outside x fun x_old => x_out (Finset.mem_erase.mpr ⟨x_is_h, x_old⟩)
    · simp only [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact at_originals x x_original
    · obtain ⟨u_ne_h, v_ne_h, edge_u_v⟩ := new_edge
      simp only [Function.update_of_ne u_ne_h, Function.update_of_ne v_ne_h] at a_selected ⊢
      exact supported u v edge_u_v
        ((before_erase_iff order tree.1 h u v u_ne_h v_ne_h).mp u_before) a a_selected

theorem rule_one_minimal_support_count_le (problem : bct) (order : List ℕ)
    (tree : is_tree_order problem order) (root : root_is_original problem order) (h y : ℕ)
    (h_hidden : h ∉ problem.originals) (edge_h_y : problem.edge h y)
    (only_neighbour : ∀ z, problem.edge h z → z = y) (listing reduced_listing : ℕ → List ℕ)
    (is_listing_old : is_listing problem listing)
    (is_listing_new : is_listing (rule_one problem h y h_hidden) reduced_listing)
    (old_nonempty : ∀ x ∈ problem.originals, (problem.domain x).Nonempty)
    (new_nonempty : ∀ x ∈ problem.originals, ((rule_one problem h y h_hidden).domain x).Nonempty)
    (tuple : ℕ → ℕ) :
    (minimal_support_models_over (rule_one problem h y h_hidden) reduced_listing (order.erase h)
      tuple).ncard ≤ (minimal_support_models_over problem listing order tuple).ncard := by
  rw [minimal_support_count_eq_selections _ reduced_listing is_listing_new new_nonempty,
    minimal_support_count_eq_selections problem listing is_listing_old old_nonempty,
    rule_one_selections problem order tree root h y h_hidden edge_h_y only_neighbour tuple]
  exact Set.ncard_image_le (selections_finite problem order tuple)

section rule_two

variable (problem : bct) (order : List ℕ) (h y z : ℕ) (h_hidden : h ∉ problem.originals)
  (edge_h_y : problem.edge h y) (edge_h_z : problem.edge h z) (y_ne_z : y ≠ z)

theorem rule_two_relation_first :
    (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).relation y z =
      joined_pairs problem h y z := by
  simp [rule_two]

theorem rule_two_relation_second :
    (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).relation z y =
      joined_pairs problem h z y := by
  have not_first : ¬ (z = y ∧ y = z) := fun both => y_ne_z both.2
  simp [rule_two, not_first]

theorem rule_two_relation_other (u v : ℕ) (not_first : ¬ (u = y ∧ v = z))
    (not_second : ¬ (u = z ∧ v = y)) :
    (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).relation u v = problem.relation u v := by
  simp [rule_two, not_first, not_second]

include h_hidden edge_h_y edge_h_z y_ne_z in
theorem parent_and_child (tree : is_tree_order problem order) (root : root_is_original problem order)
    (two_neighbours : ∀ w, problem.edge h w → w = y ∨ w = z) :
    (before order y h ∧ before order h z) ∨ (before order z h ∧ before order h y) := by
  have h_vertex := problem.edge_vertices h y edge_h_y
  obtain ⟨earlier, ⟨edge_earlier, earlier_before⟩, only⟩ :=
    hidden_parent problem order tree root h h_vertex h_hidden
  have later_side : ∀ w, problem.edge h w → w ≠ earlier → before order h w := by
    intro w edge_h_w w_ne
    have w_mem : w ∈ order := (mem_order_iff problem order tree w).mpr
      (edge_vertices_right problem h w edge_h_w)
    have h_mem : h ∈ order := (mem_order_iff problem order tree h).mpr h_vertex
    rcases before_total order h w h_mem w_mem (edge_ne problem h w edge_h_w) with first | second
    · exact first
    · exact absurd (only w ⟨problem.edge_symm _ _ edge_h_w, second⟩) w_ne
  rcases two_neighbours earlier (problem.edge_symm _ _ edge_earlier) with rfl | rfl
  · exact Or.inl ⟨earlier_before, later_side z edge_h_z y_ne_z.symm⟩
  · exact Or.inr ⟨earlier_before, later_side y edge_h_y y_ne_z⟩

theorem no_shortcut (tree : is_tree_order problem order) (parent child : ℕ)
    (edge_h_child : problem.edge h child) (parent_before : before order parent h)
    (child_after : before order h child) : ¬ problem.edge parent child := by
  intro edge_parent_child
  have parent_child := before_trans order tree.1 parent h child parent_before child_after
  have child_mem := (before_mem order h child child_after).2
  have not_head : order.head? ≠ some child := by
    intro at_head
    cases order with
    | nil => simp at at_head
    | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at at_head
      subst at_head
      rw [before_cons_iff] at child_after
      have first_new := (List.nodup_cons.mp tree.1).1
      rcases child_after with inner | ⟨_, member⟩
      · exact first_new (before_mem rest h first inner).2
      · exact first_new member
  obtain ⟨earlier, _, only⟩ := tree.2.2 child child_mem not_head
  have from_parent := only parent ⟨edge_parent_child, parent_child⟩
  have from_h := only h ⟨edge_h_child, child_after⟩
  exact before_ne order tree.1 parent h parent_before (from_parent.trans from_h.symm)

theorem rule_two_selections_from (tree : is_tree_order problem order) (parent child : ℕ)
    (pair : (parent = y ∧ child = z) ∨ (parent = z ∧ child = y))
    (two_neighbours : ∀ w, problem.edge h w → w = y ∨ w = z)
    (parent_before : before order parent h) (child_after : before order h child) (tuple : ℕ → ℕ) :
    selections (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z) (order.erase h) tuple =
      (fun selected => Function.update selected h ∅) '' selections problem order tuple := by
  have edge_h_parent : problem.edge h parent := by
    rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact edge_h_y
    · exact edge_h_z
  have edge_h_child : problem.edge h child := by
    rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact edge_h_z
    · exact edge_h_y
  have neighbour_cases : ∀ w, problem.edge h w → w = parent ∨ w = child := by
    intro w edge_h_w
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact two_neighbours w edge_h_w
    · exact (two_neighbours w edge_h_w).symm
  have pair_relation : (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).relation parent child =
      joined_pairs problem h parent child := by
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact rule_two_relation_first problem h _ _ h_hidden edge_h_y edge_h_z y_ne_z
    · exact rule_two_relation_second problem h _ _ h_hidden edge_h_y edge_h_z y_ne_z
  have pair_edge : (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).edge parent child := by
    rcases pair with both | both
    · exact Or.inr (Or.inl both)
    · exact Or.inr (Or.inr both)
  have no_old_edge : ¬ problem.edge parent child :=
    no_shortcut problem order h tree parent child edge_h_child parent_before child_after
  have not_special : ∀ u v, problem.edge u v → ¬ (u = y ∧ v = z) ∧ ¬ (u = z ∧ v = y) := by
    intro u v edge_u_v
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun both => no_old_edge (both.1 ▸ both.2 ▸ edge_u_v),
        fun both => no_old_edge (problem.edge_symm _ _ (both.1 ▸ both.2 ▸ edge_u_v))⟩
    · exact ⟨fun both => no_old_edge (problem.edge_symm _ _ (both.1 ▸ both.2 ▸ edge_u_v)),
        fun both => no_old_edge (both.1 ▸ both.2 ▸ edge_u_v)⟩
  have parent_ne_h : parent ≠ h := (edge_ne problem h parent edge_h_parent).symm
  have child_ne_h : child ≠ h := (edge_ne problem h child edge_h_child).symm
  have h_vertex : h ∈ problem.vertices := problem.edge_vertices h y edge_h_y
  have parent_vertex := edge_vertices_right problem h parent edge_h_parent
  have child_vertex := edge_vertices_right problem h child edge_h_child
  have parent_child := before_trans order tree.1 parent h child parent_before child_after
  ext reduced_selected
  constructor
  · rintro ⟨inside, outside, at_originals, supported⟩
    have at_h : reduced_selected h = ∅ := outside h (by simp [rule_two])
    let middle : Finset ℕ := (problem.domain h).filter fun c =>
      ∃ b ∈ reduced_selected child, (c, b) ∈ problem.relation h child
    refine ⟨Function.update reduced_selected h middle, ⟨fun x x_vertex => ?_, fun x x_out => ?_,
      fun x x_original => ?_, fun u v edge_u_v u_before a a_selected => ?_⟩, ?_⟩
    · by_cases x_is_h : x = h
      · subst x_is_h
        rw [Function.update_self]
        exact Finset.filter_subset _ _
      · rw [Function.update_of_ne x_is_h]
        exact inside x (Finset.mem_erase.mpr ⟨x_is_h, x_vertex⟩)
    · have x_ne_h : x ≠ h := fun same => x_out (same ▸ h_vertex)
      rw [Function.update_of_ne x_ne_h]
      exact outside x fun member => x_out (Finset.mem_of_mem_erase member)
    · rw [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact at_originals x x_original
    · by_cases u_is_h : u = h
      · subst u_is_h
        rcases neighbour_cases v edge_u_v with rfl | rfl
        · exact absurd parent_before (before_asymm order tree.1 _ _ u_before)
        · rw [Function.update_self] at a_selected
          rw [Function.update_of_ne child_ne_h]
          exact (Finset.mem_filter.mp a_selected).2
      · rw [Function.update_of_ne u_is_h] at a_selected
        by_cases v_is_h : v = h
        · subst v_is_h
          rcases neighbour_cases u (problem.edge_symm _ _ edge_u_v) with rfl | rfl
          · obtain ⟨b, b_selected, joined⟩ := supported u child pair_edge
              ((before_erase_iff order tree.1 v u child u_is_h child_ne_h).mpr parent_child) a a_selected
            rw [pair_relation] at joined
            simp only [joined_pairs, Finset.mem_filter, Finset.mem_product] at joined
            obtain ⟨_, ⟨c, c_mem, first, second⟩, _⟩ := joined
            rw [Function.update_self]
            exact ⟨c, Finset.mem_filter.mpr ⟨c_mem, b, b_selected, second⟩, first⟩
          · exact absurd child_after (before_asymm order tree.1 _ _ u_before)
        · rw [Function.update_of_ne v_is_h]
          have special := not_special u v edge_u_v
          have stated := supported u v (Or.inl ⟨u_is_h, v_is_h, edge_u_v⟩)
            ((before_erase_iff order tree.1 h u v u_is_h v_is_h).mpr u_before) a a_selected
          rw [rule_two_relation_other problem h y z h_hidden edge_h_y edge_h_z y_ne_z u v special.1
            special.2] at stated
          exact stated
    · funext x
      by_cases x_is_h : x = h
      · subst x_is_h
        simp [at_h]
      · simp [Function.update_of_ne x_is_h]
  · rintro ⟨selected, ⟨inside, outside, at_originals, supported⟩, rfl⟩
    refine ⟨fun x x_vertex => ?_, fun x x_out => ?_, fun x x_original => ?_,
      fun u v new_edge u_before a a_selected => ?_⟩
    · obtain ⟨x_ne_h, x_old⟩ := Finset.mem_erase.mp x_vertex
      simp only [Function.update_of_ne x_ne_h]
      exact inside x x_old
    · by_cases x_is_h : x = h
      · subst x_is_h
        simp
      · simp only [Function.update_of_ne x_is_h]
        exact outside x fun x_old => x_out (Finset.mem_erase.mpr ⟨x_is_h, x_old⟩)
    · simp only [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact at_originals x x_original
    · have joined_step : ∀ a ∈ selected parent, ∃ b ∈ selected child,
          (a, b) ∈ joined_pairs problem h parent child := by
        intro a a_mem
        obtain ⟨c, c_mem, first⟩ := supported parent h (problem.edge_symm _ _ edge_h_parent)
          parent_before a a_mem
        obtain ⟨b, b_mem, second⟩ := supported h child edge_h_child child_after c c_mem
        refine ⟨b, b_mem, ?_⟩
        simp only [joined_pairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨inside parent parent_vertex a_mem, inside child child_vertex b_mem⟩,
          ⟨c, inside h h_vertex c_mem, first, second⟩, fun old => absurd old no_old_edge⟩
      have pair_case : (u = parent ∧ v = child) →
          ∃ b ∈ Function.update selected h ∅ v,
            (a, b) ∈ (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).relation u v := by
        rintro ⟨rfl, rfl⟩
        simp only [Function.update_of_ne parent_ne_h] at a_selected
        rw [Function.update_of_ne child_ne_h, pair_relation]
        exact joined_step a a_selected
      have reversed_case : ¬ (u = child ∧ v = parent) := by
        rintro ⟨rfl, rfl⟩
        have old_before := (before_erase_iff order tree.1 h _ _ child_ne_h parent_ne_h).mp u_before
        exact before_asymm order tree.1 _ _ old_before parent_child
      rcases new_edge with ⟨u_ne_h, v_ne_h, edge_u_v⟩ | both | both
      · simp only [Function.update_of_ne u_ne_h, Function.update_of_ne v_ne_h] at a_selected ⊢
        have special := not_special u v edge_u_v
        rw [rule_two_relation_other problem h y z h_hidden edge_h_y edge_h_z y_ne_z u v special.1
          special.2]
        exact supported u v edge_u_v
          ((before_erase_iff order tree.1 h u v u_ne_h v_ne_h).mp u_before) a a_selected
      · rcases pair with ⟨parent_is, child_is⟩ | ⟨parent_is, child_is⟩
        · exact pair_case ⟨both.1.trans parent_is.symm, both.2.trans child_is.symm⟩
        · exact absurd ⟨both.1.trans child_is.symm, both.2.trans parent_is.symm⟩ reversed_case
      · rcases pair with ⟨parent_is, child_is⟩ | ⟨parent_is, child_is⟩
        · exact absurd ⟨both.1.trans child_is.symm, both.2.trans parent_is.symm⟩ reversed_case
        · exact pair_case ⟨both.1.trans parent_is.symm, both.2.trans child_is.symm⟩

theorem rule_two_selections (tree : is_tree_order problem order) (root : root_is_original problem order)
    (two_neighbours : ∀ w, problem.edge h w → w = y ∨ w = z) (tuple : ℕ → ℕ) :
    selections (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z) (order.erase h) tuple =
      (fun selected => Function.update selected h ∅) '' selections problem order tuple := by
  rcases parent_and_child problem order h y z h_hidden edge_h_y edge_h_z y_ne_z tree root
    two_neighbours with ⟨first, second⟩ | ⟨first, second⟩
  · exact rule_two_selections_from problem order h y z h_hidden edge_h_y edge_h_z y_ne_z tree y z
      (Or.inl ⟨rfl, rfl⟩) two_neighbours first second tuple
  · exact rule_two_selections_from problem order h y z h_hidden edge_h_y edge_h_z y_ne_z tree z y
      (Or.inr ⟨rfl, rfl⟩) two_neighbours first second tuple

theorem rule_two_minimal_support_count_le (tree : is_tree_order problem order)
    (root : root_is_original problem order)
    (two_neighbours : ∀ w, problem.edge h w → w = y ∨ w = z) (listing : ℕ → List ℕ)
    (is_listing_old : is_listing problem listing)
    (old_nonempty : ∀ x ∈ problem.originals, (problem.domain x).Nonempty) (tuple : ℕ → ℕ) :
    (minimal_support_models_over (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z) listing
      (order.erase h) tuple).ncard ≤
      (minimal_support_models_over problem listing order tuple).ncard := by
  rw [minimal_support_count_eq_selections
      (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z) listing is_listing_old old_nonempty,
    minimal_support_count_eq_selections problem listing is_listing_old old_nonempty,
    rule_two_selections problem order h y z h_hidden edge_h_y edge_h_z y_ne_z tree root two_neighbours
      tuple]
  exact Set.ncard_image_le (selections_finite problem order tuple)

theorem rule_two_tree_order (tree : is_tree_order problem order) (root : root_is_original problem order)
    (two_neighbours : ∀ w, problem.edge h w → w = y ∨ w = z) :
    is_tree_order (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z) (order.erase h) := by
  obtain ⟨parent, child, pair, parent_before, child_after⟩ : ∃ parent child,
      ((parent = y ∧ child = z) ∨ (parent = z ∧ child = y)) ∧ before order parent h ∧
        before order h child := by
    rcases parent_and_child problem order h y z h_hidden edge_h_y edge_h_z y_ne_z tree root
      two_neighbours with both | both
    · exact ⟨y, z, Or.inl ⟨rfl, rfl⟩, both⟩
    · exact ⟨z, y, Or.inr ⟨rfl, rfl⟩, both⟩
  have edge_h_parent : problem.edge h parent := by
    rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact edge_h_y
    · exact edge_h_z
  have edge_h_child : problem.edge h child := by
    rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact edge_h_z
    · exact edge_h_y
  have neighbour_cases : ∀ w, problem.edge h w → w = parent ∨ w = child := by
    intro w edge_h_w
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact two_neighbours w edge_h_w
    · exact (two_neighbours w edge_h_w).symm
  have edge_cases : ∀ u v, (rule_two problem h y z h_hidden edge_h_y edge_h_z y_ne_z).edge u v ↔
      (u ≠ h ∧ v ≠ h ∧ problem.edge u v) ∨ (u = parent ∧ v = child) ∨ (u = child ∧ v = parent) := by
    intro u v
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact or_congr_right or_comm
  have parent_ne_h : parent ≠ h := (edge_ne problem h parent edge_h_parent).symm
  have child_ne_h : child ≠ h := (edge_ne problem h child edge_h_child).symm
  have parent_child := before_trans order tree.1 parent h child parent_before child_after
  refine ⟨tree.1.erase h, ?_, fun later later_mem not_head => ?_⟩
  · rw [erase_toFinset order tree.1 h, tree.2.1]
    rfl
  · obtain ⟨later_ne, later_old⟩ := tree.1.mem_erase_iff.mp later_mem
    rw [erase_head order h (hidden_not_head problem order root h h_hidden)] at not_head
    obtain ⟨earlier, ⟨edge_earlier, earlier_before⟩, only⟩ := tree.2.2 later later_old not_head
    by_cases earlier_is_h : earlier = h
    · subst earlier_is_h
      have later_is_child : later = child := by
        rcases neighbour_cases later edge_earlier with rfl | rfl
        · exact absurd parent_before (before_asymm order tree.1 _ _ earlier_before)
        · rfl
      subst later_is_child
      refine ⟨parent, ⟨(edge_cases parent later).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        (before_erase_iff order tree.1 earlier parent later parent_ne_h later_ne).mpr parent_child⟩, ?_⟩
      rintro other ⟨new_edge, other_before⟩
      rcases (edge_cases other later).mp new_edge with ⟨other_ne, _, edge_other⟩ | both | both
      · have old_before := (before_erase_iff order tree.1 earlier other later other_ne later_ne).mp
          other_before
        exact absurd (only other ⟨edge_other, old_before⟩) other_ne
      · exact both.1
      · exact absurd both.2 (before_ne order tree.1 parent later parent_child).symm
    · refine ⟨earlier, ⟨(edge_cases earlier later).mpr (Or.inl ⟨earlier_is_h, later_ne, edge_earlier⟩),
        (before_erase_iff order tree.1 h earlier later earlier_is_h later_ne).mpr earlier_before⟩, ?_⟩
      rintro other ⟨new_edge, other_before⟩
      rcases (edge_cases other later).mp new_edge with ⟨other_ne, _, edge_other⟩ | both | both
      · exact only other ⟨edge_other,
          (before_erase_iff order tree.1 h other later other_ne later_ne).mp other_before⟩
      · obtain ⟨rfl, rfl⟩ := both
        exact absurd (only h ⟨edge_h_child, child_after⟩).symm earlier_is_h
      · obtain ⟨rfl, rfl⟩ := both
        have old_before := (before_erase_iff order tree.1 h _ _ child_ne_h parent_ne_h).mp other_before
        exact absurd parent_child (before_asymm order tree.1 _ _ old_before)

end rule_two

end rules
end parsimony
