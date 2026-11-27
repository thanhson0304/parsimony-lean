import parsimony.rules.grouping_reduced
import parsimony.rules.dtbe

namespace parsimony
namespace rules

open scoped Classical

theorem before_of_split (first rest : List ℕ) (x y : ℕ) (y_first : y ∈ first) :
    before (first ++ x :: rest) y x := by
  unfold before
  have pieces : List.Sublist ([y] ++ [x]) (first ++ x :: rest) :=
    (List.singleton_sublist.mpr y_first).append (List.singleton_sublist.mpr (by simp))
  simpa using pieces

theorem mem_first_of_before (first rest : List ℕ) (x y : ℕ) (nodup : (first ++ x :: rest).Nodup)
    (y_before : before (first ++ x :: rest) y x) : y ∈ first := by
  have y_mem := (before_mem _ _ _ y_before).1
  rcases List.mem_append.mp y_mem with in_first | in_rest
  · exact in_first
  · rcases List.mem_cons.mp in_rest with rfl | in_tail
    · exact absurd rfl (before_ne _ nodup _ _ y_before)
    · have x_before : before (first ++ x :: rest) x y := by
        unfold before
        have inner : List.Sublist [x, y] (x :: rest) :=
          (List.singleton_sublist.mpr in_tail).cons_cons x
        exact inner.trans (List.sublist_append_right first _)
      exact absurd x_before (before_asymm _ nodup _ _ y_before)

theorem head_before (order : List ℕ) (nodup : order.Nodup) (root x : ℕ) (at_head : order.head? = some root)
    (x_before : before order x root) : False := by
  cases order with
  | nil => simp at at_head
  | cons first rest =>
    simp only [List.head?_cons, Option.some.injEq] at at_head
    subst at_head
    rw [before_cons_iff] at x_before
    have first_new := (List.nodup_cons.mp nodup).1
    rcases x_before with inner | ⟨_, member⟩
    · exact first_new (before_mem rest x first inner).2
    · exact first_new member

theorem prefix_choice (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (tuple : ℕ → ℕ) (selected : ℕ → Finset ℕ)
    (selection : is_selection problem order tuple selected) (first : List ℕ) :
    ∀ rest, order = first ++ rest → ∃ chosen : ℕ → ℕ, (∀ x ∈ first, chosen x ∈ selected x) ∧
      ∀ u ∈ first, ∀ v ∈ first, problem.edge u v → (chosen u, chosen v) ∈ problem.relation u v := by
  induction first using List.reverseRecOn with
  | nil =>
    intro _ _
    exact ⟨fun _ => 0, by simp, by simp⟩
  | append_singleton first x hypothesis =>
    intro rest whole
    have split : order = first ++ x :: rest := by simpa using whole
    obtain ⟨chosen, chosen_mem, chosen_holds⟩ := hypothesis (x :: rest) split
    have nodup : (first ++ x :: rest).Nodup := split ▸ tree.1
    have x_new : x ∉ first := by
      intro member
      exact List.disjoint_of_nodup_append nodup member (by simp)
    by_cases at_head : order.head? = some x
    · have first_empty : first = [] := by
        cases first with
        | nil => rfl
        | cons other others =>
          rw [split] at at_head
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at at_head
          exact absurd (by simp [at_head]) x_new
      obtain ⟨top, top_head, top_original⟩ := root
      rw [at_head, Option.some.injEq] at top_head
      subst top_head
      subst first_empty
      refine ⟨fun _ => tuple x, ?_, ?_⟩
      · intro y y_mem
        have y_is : y = x := by simpa using y_mem
        subst y_is
        rw [selection.2.2.1 y top_original]
        exact Finset.mem_singleton_self _
      · intro u u_mem v v_mem edge_u_v
        have u_is : u = x := by simpa using u_mem
        have v_is : v = x := by simpa using v_mem
        subst u_is v_is
        exact absurd edge_u_v (problem.edge_irrefl _)
    · have x_mem : x ∈ order := by simp [split]
      obtain ⟨parent, ⟨edge_parent, parent_before⟩, only⟩ := tree.2.2 x x_mem at_head
      have parent_first : parent ∈ first := by
        rw [split] at parent_before
        exact mem_first_of_before first rest x parent nodup parent_before
      obtain ⟨b, b_selected, allowed⟩ := selection.2.2.2 parent x edge_parent parent_before _
        (chosen_mem parent parent_first)
      have keep : ∀ y ∈ first, Function.update chosen x b y = chosen y := by
        intro y y_first
        have y_ne : y ≠ x := fun same => x_new (same ▸ y_first)
        exact Function.update_of_ne y_ne _ _
      have to_x : ∀ y ∈ first, problem.edge y x → (chosen y, b) ∈ problem.relation y x := by
        intro y y_first edge_y_x
        have y_before : before order y x := by
          rw [split]
          exact before_of_split first rest x y y_first
        rw [only y ⟨edge_y_x, y_before⟩]
        exact allowed
      refine ⟨Function.update chosen x b, ?_, ?_⟩
      · intro y y_mem
        rcases List.mem_append.mp y_mem with y_first | y_last
        · rw [keep y y_first]
          exact chosen_mem y y_first
        · have y_is : y = x := by simpa using y_last
          subst y_is
          rw [Function.update_self]
          exact b_selected
      · intro u u_mem v v_mem edge_u_v
        rcases List.mem_append.mp u_mem with u_first | u_last
        · rcases List.mem_append.mp v_mem with v_first | v_last
          · rw [keep u u_first, keep v v_first]
            exact chosen_holds u u_first v v_first edge_u_v
          · have v_is : v = x := by simpa using v_last
            subst v_is
            rw [keep u u_first, Function.update_self]
            exact to_x u u_first edge_u_v
        · have u_is : u = x := by simpa using u_last
          subst u_is
          rcases List.mem_append.mp v_mem with v_first | v_last
          · rw [keep v v_first, Function.update_self]
            exact (problem.relation_symm _ _ _ _).mp (to_x v v_first (problem.edge_symm _ _ edge_u_v))
          · have v_is : v = u := by simpa using v_last
            subst v_is
            exact absurd edge_u_v (problem.edge_irrefl _)

theorem selections_nonempty_iff (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (tuple : ℕ → ℕ) :
    (selections problem order tuple).Nonempty ↔ in_relation problem tuple := by
  constructor
  · rintro ⟨selected, selection⟩
    obtain ⟨chosen, chosen_mem, chosen_holds⟩ := prefix_choice problem order tree root tuple selected
      selection order [] (by simp)
    have in_order : ∀ x, x ∈ problem.vertices → x ∈ order := fun x x_vertex =>
      (mem_order_iff problem order tree x).mpr x_vertex
    refine ⟨fun x => if x ∈ problem.vertices then chosen x else 0, ⟨fun x x_vertex => ?_,
      fun x x_out => ?_, fun u v edge_u_v => ?_⟩, fun x x_original => ?_⟩
    · simp only [x_vertex, ite_true]
      exact selection.1 x x_vertex (chosen_mem x (in_order x x_vertex))
    · simp [x_out]
    · have u_vertex := problem.edge_vertices u v edge_u_v
      have v_vertex := edge_vertices_right problem u v edge_u_v
      simp only [u_vertex, v_vertex, ite_true]
      exact chosen_holds u (in_order u u_vertex) v (in_order v v_vertex) edge_u_v
    · have x_vertex := problem.originals_subset x_original
      simp only [x_vertex, ite_true]
      have member := chosen_mem x (in_order x x_vertex)
      rw [selection.2.2.1 x x_original, Finset.mem_singleton] at member
      exact member
  · rintro ⟨candidate, ⟨inside, outside, holds⟩, agrees⟩
    refine ⟨fun x => if x ∈ problem.vertices then {candidate x} else ∅, fun x x_vertex => ?_,
      fun x x_out => ?_, fun x x_original => ?_, fun x y edge_x_y _ a a_selected => ?_⟩
    · simp only [x_vertex, ite_true, Finset.singleton_subset_iff]
      exact inside x x_vertex
    · simp [x_out]
    · simp only [problem.originals_subset x_original, ite_true]
      rw [agrees x x_original]
    · have x_vertex := problem.edge_vertices x y edge_x_y
      have y_vertex := edge_vertices_right problem x y edge_x_y
      simp only [x_vertex, ite_true, Finset.mem_singleton] at a_selected
      subst a_selected
      refine ⟨candidate y, ?_, holds x y edge_x_y⟩
      simp [y_vertex]

def is_minimal_support_exact (problem : bct) (listing : ℕ → List ℕ) (order : List ℕ) : Prop :=
  (∀ valuation ∈ minimal_support_models problem listing order,
    ∃ tuple, encodes_tuple problem valuation tuple ∧ in_relation problem tuple) ∧
  ∀ tuple, in_relation problem tuple →
    ∃ valuation ∈ minimal_support_models problem listing order, encodes_tuple problem valuation tuple

theorem minimal_support_exact (problem : bct) (listing : ℕ → List ℕ)
    (is_listing_listing : is_listing problem listing)
    (nonempty : ∀ x ∈ problem.originals, (problem.domain x).Nonempty) (order : List ℕ)
    (tree : is_tree_order problem order) (root : root_is_original problem order) :
    is_minimal_support_exact problem listing order := by
  have over_tuple : ∀ tuple, (minimal_support_models_over problem listing order tuple).Nonempty ↔
      in_relation problem tuple := by
    intro tuple
    rw [minimal_support_models_eq_image problem listing is_listing_listing nonempty order tuple,
      Set.image_nonempty]
    exact selections_nonempty_iff problem order tree root tuple
  constructor
  · intro valuation model
    have decoded : ∀ x, ∃ a, x ∈ problem.originals → ∀ b ∈ problem.domain x,
        valuation (Sum.inl (x, b)) = decide (b = a) := by
      intro x
      by_cases x_original : x ∈ problem.originals
      · obtain ⟨chosen, at_values, _⟩ := (ladder_holds_iff problem listing is_listing_listing x
          (nonempty x x_original) valuation).mp
          fun clause clause_mem => model.2 clause (Or.inl ⟨x, x_original, clause_mem⟩)
        refine ⟨value_at listing x chosen, fun _ b b_mem => ?_⟩
        obtain ⟨position, position_lt, rfl⟩ := List.getElem_of_mem
          ((mem_listing problem listing is_listing_listing x b).mpr b_mem)
        have stated := at_values ⟨position, position_lt⟩
        refine stated.trans ?_
        congr 1
        rw [eq_iff_iff]
        constructor
        · rintro rfl
          rfl
        · intro same
          apply Fin.ext
          have inner : (listing x)[position] = (listing x)[chosen.val] := same
          exact ((is_listing_listing x).1.getElem_inj_iff).mp inner
      · exact ⟨0, fun impossible => absurd impossible x_original⟩
    choose tuple tuple_spec using decoded
    have encodes : encodes_tuple problem valuation tuple := fun x x_original b b_mem =>
      tuple_spec x x_original b b_mem
    exact ⟨tuple, encodes, (over_tuple tuple).mp ⟨valuation, model, encodes⟩⟩
  · intro tuple relation
    obtain ⟨valuation, model, encodes⟩ := (over_tuple tuple).mpr relation
    exact ⟨valuation, model, encodes⟩

theorem rule_three_tree_order (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (h k : ℕ) (name : ℕ × ℕ → ℕ)
    (k_hidden : k ∉ problem.originals) (edge_h_k : problem.edge h k) (h_before : before order h k) :
    is_tree_order (rule_three problem h k name k_hidden edge_h_k) (order.erase k) := by
  have h_ne_k : h ≠ k := edge_ne problem h k edge_h_k
  have k_vertex := edge_vertices_right problem h k edge_h_k
  obtain ⟨k_parent, _, k_only⟩ := hidden_parent problem order tree root k k_vertex k_hidden
  have h_is_parent := k_only h ⟨edge_h_k, h_before⟩
  have parent_of_k : ∀ w, problem.edge w k → before order w k → w = h := fun w edge_w_k w_before =>
    (k_only w ⟨edge_w_k, w_before⟩).trans h_is_parent.symm
  refine ⟨tree.1.erase k, ?_, fun later later_mem not_head => ?_⟩
  · rw [erase_toFinset order tree.1 k, tree.2.1]
    rfl
  · obtain ⟨later_ne, later_old⟩ := tree.1.mem_erase_iff.mp later_mem
    rw [erase_head order k (hidden_not_head problem order root k k_hidden)] at not_head
    obtain ⟨earlier, ⟨edge_earlier, earlier_before⟩, only⟩ := tree.2.2 later later_old not_head
    have keep := fun x x_ne => before_erase_iff order tree.1 k x later x_ne later_ne
    have from_h : ∀ other, other ≠ k → problem.edge k later → other = h → before order other later →
        earlier = k ∧ before order k later := by
      intro other _ edge_k_later other_is other_before
      subst other_is
      have k_mem : k ∈ order := (mem_order_iff problem order tree k).mpr k_vertex
      rcases before_total order k later k_mem later_old later_ne.symm with k_first | later_first
      · exact ⟨(only k ⟨edge_k_later, k_first⟩).symm, k_first⟩
      · have later_is := parent_of_k later (problem.edge_symm _ _ edge_k_later) later_first
        exact absurd later_is.symm (before_ne order tree.1 _ _ other_before)
    have into_h : ∀ other, later = h → problem.edge other k → other ≠ later →
        before order other later → False := by
      intro other later_is edge_other_k other_ne other_before
      subst later_is
      have to_k := before_trans order tree.1 other later k other_before h_before
      exact other_ne (parent_of_k other edge_other_k to_k)
    by_cases earlier_is_k : earlier = k
    · subst earlier_is_k
      have h_before_later := before_trans order tree.1 h earlier later h_before earlier_before
      have h_ne_later : h ≠ later := before_ne order tree.1 h later h_before_later
      refine ⟨h, ⟨⟨h_ne_later, h_ne_k, later_ne, Or.inr (Or.inl ⟨rfl, edge_earlier⟩)⟩,
        (keep h h_ne_k).mpr h_before_later⟩, ?_⟩
      rintro other ⟨⟨other_ne_later, other_ne_k, _, kinds⟩, other_before⟩
      have old_before := (keep other other_ne_k).mp other_before
      rcases kinds with plain | both | both
      · exact absurd (only other ⟨plain, old_before⟩) other_ne_k
      · exact both.1
      · exact (into_h other both.1 both.2 other_ne_later old_before).elim
    · refine ⟨earlier, ⟨⟨edge_ne problem earlier later edge_earlier, earlier_is_k, later_ne,
        Or.inl edge_earlier⟩, (keep earlier earlier_is_k).mpr earlier_before⟩, ?_⟩
      rintro other ⟨⟨other_ne_later, other_ne_k, _, kinds⟩, other_before⟩
      have old_before := (keep other other_ne_k).mp other_before
      rcases kinds with plain | both | both
      · exact only other ⟨plain, old_before⟩
      · exact absurd (from_h other other_ne_k both.2 both.1 old_before).1 earlier_is_k
      · exact (into_h other both.1 both.2 other_ne_later old_before).elim

theorem swapped_rule_three_tree_order (problem : bct) (order : List ℕ) (tree : is_tree_order problem order)
    (root : root_is_original problem order) (h k : ℕ) (name : ℕ × ℕ → ℕ)
    (h_hidden : h ∉ problem.originals) (k_hidden : k ∉ problem.originals)
    (edge_h_k : problem.edge h k) (k_before : before order k h) :
    ∃ reduced_order, is_tree_order (rule_three problem h k name k_hidden edge_h_k) reduced_order ∧
      reduced_order.head? = order.head? := by
  have h_ne_k : h ≠ k := edge_ne problem h k edge_h_k
  have h_vertex := problem.edge_vertices h k edge_h_k
  have k_vertex := edge_vertices_right problem h k edge_h_k
  let rename : ℕ → ℕ := fun x => if x = k then h else x
  let shorter := order.erase h
  have shorter_nodup : shorter.Nodup := tree.1.erase h
  have h_not_shorter : h ∉ shorter := fun member => (tree.1.mem_erase_iff.mp member).1 rfl
  have rename_other : ∀ x, x ≠ k → rename x = x := fun x x_ne => by simp [rename, x_ne]
  have rename_k : rename k = h := by simp [rename]
  have rename_injective : Set.InjOn rename {x | x ∈ shorter} := by
    intro first first_mem second second_mem same
    by_cases first_is : first = k
    · by_cases second_is : second = k
      · rw [first_is, second_is]
      · subst first_is
        rw [rename_k, rename_other second second_is] at same
        exact absurd (same ▸ second_mem) h_not_shorter
    · by_cases second_is : second = k
      · subst second_is
        rw [rename_k, rename_other first first_is] at same
        exact absurd (same ▸ first_mem) h_not_shorter
      · rwa [rename_other first first_is, rename_other second second_is] at same
  have mapped_before : ∀ x y, x ∈ shorter → y ∈ shorter →
      (before (shorter.map rename) (rename x) (rename y) ↔ before shorter x y) := by
    intro x y x_mem y_mem
    constructor
    · intro mapped
      rcases eq_or_ne x y with rfl | x_ne_y
      · have mapped_nodup : (shorter.map rename).Nodup :=
          (List.nodup_map_iff_inj_on shorter_nodup).mpr fun a a_mem b b_mem same =>
            rename_injective a_mem b_mem same
        exact absurd rfl (before_ne _ mapped_nodup _ _ mapped)
      · rcases before_total shorter x y x_mem y_mem x_ne_y with forward | backward
        · exact forward
        · have mapped_nodup : (shorter.map rename).Nodup :=
            (List.nodup_map_iff_inj_on shorter_nodup).mpr fun a a_mem b b_mem same =>
              rename_injective a_mem b_mem same
          have back : before (shorter.map rename) (rename y) (rename x) := by
            have mapped_back := List.Sublist.map rename backward
            simpa [before] using mapped_back
          exact (before_asymm _ mapped_nodup _ _ mapped back).elim
    · intro plain
      have mapped := List.Sublist.map rename plain
      simpa [before] using mapped
  obtain ⟨h_parent, _, h_only⟩ := hidden_parent problem order tree root h h_vertex h_hidden
  have k_is_parent := h_only k ⟨problem.edge_symm _ _ edge_h_k, k_before⟩
  have parent_of_h : ∀ w, problem.edge w h → before order w h → w = k := fun w edge_w_h w_before =>
    (h_only w ⟨edge_w_h, w_before⟩).trans k_is_parent.symm
  have k_shorter : k ∈ shorter :=
    tree.1.mem_erase_iff.mpr ⟨h_ne_k.symm, (mem_order_iff problem order tree k).mpr k_vertex⟩
  refine ⟨shorter.map rename, ⟨(List.nodup_map_iff_inj_on shorter_nodup).mpr fun a a_mem b b_mem same =>
    rename_injective a_mem b_mem same, ?_, ?_⟩, ?_⟩
  · ext x
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨y, y_mem, rfl⟩
      obtain ⟨y_ne_h, y_old⟩ := tree.1.mem_erase_iff.mp y_mem
      have y_vertex := (mem_order_iff problem order tree y).mp y_old
      by_cases y_is_k : y = k
      · rw [y_is_k, rename_k]
        exact Finset.mem_erase.mpr ⟨h_ne_k, h_vertex⟩
      · rw [rename_other y y_is_k]
        exact Finset.mem_erase.mpr ⟨y_is_k, y_vertex⟩
    · intro x_new
      obtain ⟨x_ne_k, x_vertex⟩ := Finset.mem_erase.mp x_new
      by_cases x_is_h : x = h
      · subst x_is_h
        exact ⟨k, k_shorter, rename_k⟩
      · exact ⟨x, tree.1.mem_erase_iff.mpr ⟨x_is_h, (mem_order_iff problem order tree x).mpr x_vertex⟩,
          rename_other x x_ne_k⟩
  · intro later later_mem not_head
    obtain ⟨y, y_mem, rfl⟩ := List.mem_map.mp later_mem
    obtain ⟨y_ne_h, y_old⟩ := tree.1.mem_erase_iff.mp y_mem
    have keep := fun x x_ne => before_erase_iff order tree.1 h x y x_ne y_ne_h
    have y_not_head : order.head? ≠ some y := by
      intro at_head
      apply not_head
      rw [List.head?_map, erase_head order h (hidden_not_head problem order root h h_hidden), at_head]
      rfl
    obtain ⟨earlier, ⟨edge_earlier, earlier_before⟩, only⟩ := tree.2.2 y y_old y_not_head
    have member_of : ∀ other,
        (rule_three problem h k name k_hidden edge_h_k).edge other (rename y) →
        before (shorter.map rename) other (rename y) → ∃ z ∈ shorter, other = rename z ∧ before shorter z y := by
      intro other _ other_before
      obtain ⟨z, z_mem, rfl⟩ := List.mem_map.mp (before_mem _ _ _ other_before).1
      exact ⟨z, z_mem, rfl, (mapped_before z y z_mem y_mem).mp other_before⟩
    by_cases y_is_k : y = k
    · subst y_is_k
      have earlier_ne_h : earlier ≠ h := by
        rintro rfl
        exact before_asymm order tree.1 _ _ earlier_before k_before
      have earlier_ne_y : earlier ≠ y := edge_ne problem earlier y edge_earlier
      have earlier_shorter : earlier ∈ shorter :=
        tree.1.mem_erase_iff.mpr ⟨earlier_ne_h, (before_mem _ _ _ earlier_before).1⟩
      refine ⟨earlier, ⟨?_, ?_⟩, ?_⟩
      · show (rule_three problem h y name k_hidden edge_h_k).edge earlier (rename y)
        rw [rename_k]
        exact ⟨earlier_ne_h, earlier_ne_y, h_ne_k, Or.inr (Or.inr ⟨rfl, edge_earlier⟩)⟩
      · have mapped := (mapped_before earlier y earlier_shorter y_mem).mpr
          ((keep earlier earlier_ne_h).mpr earlier_before)
        rwa [rename_other earlier earlier_ne_y] at mapped
      · rintro other ⟨new_edge, other_before⟩
        obtain ⟨z, z_mem, rfl, z_before⟩ := member_of other new_edge other_before
        obtain ⟨z_ne_h, z_old⟩ := tree.1.mem_erase_iff.mp z_mem
        have z_old_before := (keep z z_ne_h).mp z_before
        have z_ne_y : z ≠ y := before_ne order tree.1 z y z_old_before
        rw [rename_other z z_ne_y] at new_edge ⊢
        rw [rename_k] at new_edge
        rcases new_edge.2.2.2 with plain | both | both
        · exact absurd (parent_of_h z plain (before_trans order tree.1 z y h z_old_before k_before)) z_ne_y
        · exact absurd both.1 z_ne_h
        · exact only z ⟨both.2, z_old_before⟩
    · have renamed_y := rename_other y y_is_k
      by_cases earlier_is_h : earlier = h
      · subst earlier_is_h
        have k_before_y := before_trans order tree.1 k earlier y k_before earlier_before
        refine ⟨earlier, ⟨?_, ?_⟩, ?_⟩
        · show (rule_three problem earlier k name k_hidden edge_h_k).edge earlier (rename y)
          rw [renamed_y]
          exact ⟨edge_ne problem earlier y edge_earlier, h_ne_k, y_is_k, Or.inl edge_earlier⟩
        · have mapped := (mapped_before k y k_shorter y_mem).mpr
            ((keep k h_ne_k.symm).mpr k_before_y)
          rwa [rename_k] at mapped
        · rintro other ⟨new_edge, other_before⟩
          obtain ⟨z, z_mem, rfl, z_before⟩ := member_of other new_edge other_before
          obtain ⟨z_ne_h, z_old⟩ := tree.1.mem_erase_iff.mp z_mem
          have z_old_before := (keep z z_ne_h).mp z_before
          by_cases z_is_k : z = k
          · rw [z_is_k, rename_k]
          · rw [rename_other z z_is_k, renamed_y] at new_edge
            rcases new_edge.2.2.2 with plain | both | both
            · exact absurd (only z ⟨plain, z_old_before⟩) z_ne_h
            · exact absurd both.1 z_ne_h
            · exact absurd both.1 y_ne_h
      · by_cases earlier_is_k : earlier = k
        · subst earlier_is_k
          refine ⟨h, ⟨?_, ?_⟩, ?_⟩
          · show (rule_three problem h earlier name k_hidden edge_h_k).edge h (rename y)
            rw [renamed_y]
            exact ⟨y_ne_h.symm, h_ne_k, y_is_k, Or.inr (Or.inl ⟨rfl, edge_earlier⟩)⟩
          · have mapped := (mapped_before earlier y k_shorter y_mem).mpr
              ((keep earlier h_ne_k.symm).mpr earlier_before)
            rwa [rename_k] at mapped
          · rintro other ⟨new_edge, other_before⟩
            obtain ⟨z, z_mem, rfl, z_before⟩ := member_of other new_edge other_before
            obtain ⟨z_ne_h, z_old⟩ := tree.1.mem_erase_iff.mp z_mem
            have z_old_before := (keep z z_ne_h).mp z_before
            by_cases z_is_k : z = earlier
            · rw [z_is_k, rename_k]
            · rw [rename_other z z_is_k, renamed_y] at new_edge
              rcases new_edge.2.2.2 with plain | both | both
              · exact absurd (only z ⟨plain, z_old_before⟩) z_is_k
              · exact absurd both.1 z_ne_h
              · exact absurd both.1 y_ne_h
        · have earlier_shorter : earlier ∈ shorter :=
            tree.1.mem_erase_iff.mpr ⟨earlier_is_h, (before_mem _ _ _ earlier_before).1⟩
          refine ⟨earlier, ⟨?_, ?_⟩, ?_⟩
          · show (rule_three problem h k name k_hidden edge_h_k).edge earlier (rename y)
            rw [renamed_y]
            exact ⟨edge_ne problem earlier y edge_earlier, earlier_is_k, y_is_k, Or.inl edge_earlier⟩
          · have mapped := (mapped_before earlier y earlier_shorter y_mem).mpr
              ((keep earlier earlier_is_h).mpr earlier_before)
            rwa [rename_other earlier earlier_is_k] at mapped
          · rintro other ⟨new_edge, other_before⟩
            obtain ⟨z, z_mem, rfl, z_before⟩ := member_of other new_edge other_before
            obtain ⟨z_ne_h, z_old⟩ := tree.1.mem_erase_iff.mp z_mem
            have z_old_before := (keep z z_ne_h).mp z_before
            have h_side : problem.edge h y → False := by
              intro edge_h_y
              have h_mem : h ∈ order := (mem_order_iff problem order tree h).mpr h_vertex
              rcases before_total order h y h_mem y_old y_ne_h.symm with h_first | y_first
              · exact earlier_is_h (only h ⟨edge_h_y, h_first⟩).symm
              · exact y_is_k (parent_of_h y (problem.edge_symm _ _ edge_h_y) y_first)
            by_cases z_is_k : z = k
            · subst z_is_k
              rw [rename_k, renamed_y] at new_edge
              rcases new_edge.2.2.2 with plain | both | both
              · exact (h_side plain).elim
              · exact absurd (only z ⟨both.2, z_old_before⟩).symm earlier_is_k
              · exact absurd both.1 y_ne_h
            · rw [rename_other z z_is_k, renamed_y] at new_edge
              rw [rename_other z z_is_k]
              rcases new_edge.2.2.2 with plain | both | both
              · exact only z ⟨plain, z_old_before⟩
              · exact absurd both.1 z_ne_h
              · exact absurd both.1 y_ne_h
  · rw [List.head?_map, erase_head order h (hidden_not_head problem order root h h_hidden)]
    obtain ⟨top, at_head, top_original⟩ := root
    rw [at_head]
    have top_ne : top ≠ k := original_ne_hidden k_hidden top_original
    simp [rename, top_ne]

theorem any_step_keeps_tree_order (problem reduced : bct) (step : is_any_step problem reduced)
    (order : List ℕ) (tree : is_tree_order problem order) (root : root_is_original problem order) :
    ∃ reduced_order, is_tree_order reduced reduced_order ∧ reduced_order.head? = order.head? ∧
      root_is_original reduced reduced_order := by
  have carry : ∀ reduced_order, reduced_order.head? = order.head? →
      reduced.originals = problem.originals → root_is_original reduced reduced_order := by
    intro reduced_order same_head same_originals
    obtain ⟨top, at_head, top_original⟩ := root
    exact ⟨top, same_head.trans at_head, same_originals ▸ top_original⟩
  rcases step with ⟨h, y, h_hidden, edge_h_y, only_neighbour, rfl⟩ |
    ⟨h, y, z, h_hidden, edge_h_y, edge_h_z, y_ne_z, two_neighbours, rfl⟩ |
    ⟨h, k, name, h_hidden, k_hidden, edge_h_k, _, rfl⟩ |
    ⟨h, table, name, _, _, _, _, rfl⟩
  · have same_head := erase_head order h (hidden_not_head problem order root h h_hidden)
    exact ⟨order.erase h, rule_one_tree_order problem order tree root h y h_hidden edge_h_y
      only_neighbour, same_head, carry _ same_head rfl⟩
  · have same_head := erase_head order h (hidden_not_head problem order root h h_hidden)
    exact ⟨order.erase h, rule_two_tree_order problem order h y z h_hidden edge_h_y edge_h_z y_ne_z tree
      root two_neighbours, same_head, carry _ same_head rfl⟩
  · have h_mem := (mem_order_iff problem order tree h).mpr (problem.edge_vertices h k edge_h_k)
    have k_mem := (mem_order_iff problem order tree k).mpr (edge_vertices_right problem h k edge_h_k)
    rcases before_total order h k h_mem k_mem (edge_ne problem h k edge_h_k) with first | second
    · have same_head := erase_head order k (hidden_not_head problem order root k k_hidden)
      exact ⟨order.erase k, rule_three_tree_order problem order tree root h k name k_hidden edge_h_k
        first, same_head, carry _ same_head rfl⟩
    · obtain ⟨reduced_order, reduced_tree, same_head⟩ := swapped_rule_three_tree_order problem order tree
        root h k name h_hidden k_hidden edge_h_k second
      exact ⟨reduced_order, reduced_tree, same_head, carry _ same_head rfl⟩
  · exact ⟨order, tree, rfl, carry order rfl rfl⟩

theorem any_steps_keep_tree_order (problem reduced : bct)
    (steps : Relation.ReflTransGen is_any_step problem reduced) (order : List ℕ)
    (tree : is_tree_order problem order) (root : root_is_original problem order) :
    ∃ reduced_order, is_tree_order reduced reduced_order ∧ reduced_order.head? = order.head? ∧
      root_is_original reduced reduced_order := by
  induction steps with
  | refl => exact ⟨order, tree, rfl, root⟩
  | tail _ last hypothesis =>
    obtain ⟨middle_order, middle_tree, middle_head, middle_root⟩ := hypothesis
    obtain ⟨reduced_order, reduced_tree, reduced_head, reduced_root⟩ :=
      any_step_keeps_tree_order _ _ last middle_order middle_tree middle_root
    exact ⟨reduced_order, reduced_tree, reduced_head.trans middle_head, reduced_root⟩

theorem reduced_minimal_support_exact_for_original_relation (problem reduced : bct)
    (steps : Relation.ReflTransGen is_any_step problem reduced) (order : List ℕ)
    (tree : is_tree_order problem order) (root : root_is_original problem order)
    (listing : ℕ → List ℕ) (is_listing_listing : is_listing reduced listing)
    (nonempty : ∀ x ∈ reduced.originals, (reduced.domain x).Nonempty) :
    ∃ reduced_order, is_tree_order reduced reduced_order ∧ reduced_order.head? = order.head? ∧
      is_minimal_support_exact reduced listing reduced_order ∧
      ∀ tuple, in_relation reduced tuple ↔ in_relation problem tuple := by
  obtain ⟨reduced_order, reduced_tree, reduced_head, reduced_root⟩ :=
    any_steps_keep_tree_order problem reduced steps order tree root
  exact ⟨reduced_order, reduced_tree, reduced_head,
    minimal_support_exact reduced listing is_listing_listing nonempty reduced_order reduced_tree
      reduced_root, fun tuple => (any_steps_counts problem reduced steps tuple).2⟩

end rules
end parsimony
