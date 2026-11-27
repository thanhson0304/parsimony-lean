import parsimony.rules.basic

namespace parsimony
namespace rules

open scoped Classical

noncomputable def allowed_pairs (problem : bct) (h k : ℕ) : Finset (ℕ × ℕ) :=
  (problem.domain h ×ˢ problem.domain k).filter fun pair => pair ∈ problem.relation h k

noncomputable def merged_side (problem : bct) (h k : ℕ) (name : ℕ × ℕ → ℕ) (z : ℕ) : Finset (ℕ × ℕ) :=
  ((allowed_pairs problem h k ×ˢ problem.domain z).filter fun entry =>
    (problem.edge h z → (entry.1.1, entry.2) ∈ problem.relation h z) ∧
      (problem.edge k z → (entry.1.2, entry.2) ∈ problem.relation k z)).image
    fun entry => (name entry.1, entry.2)

noncomputable def rule_three (problem : bct) (h k : ℕ) (name : ℕ × ℕ → ℕ)
    (k_hidden : k ∉ problem.originals) (edge_h_k : problem.edge h k) : bct where
  vertices := problem.vertices.erase k
  originals := problem.originals
  originals_subset := fun _ x_original =>
    Finset.mem_erase.mpr ⟨original_ne_hidden k_hidden x_original, problem.originals_subset x_original⟩
  domain := fun x => if x = h then (allowed_pairs problem h k).image name else problem.domain x
  edge := fun u v => u ≠ v ∧ u ≠ k ∧ v ≠ k ∧
    (problem.edge u v ∨ (u = h ∧ problem.edge k v) ∨ (v = h ∧ problem.edge u k))
  edge_symm := by
    rintro u v ⟨u_ne_v, u_ne_k, v_ne_k, kinds⟩
    refine ⟨u_ne_v.symm, v_ne_k, u_ne_k, ?_⟩
    rcases kinds with plain | both | both
    · exact Or.inl (problem.edge_symm _ _ plain)
    · exact Or.inr (Or.inr ⟨both.1, problem.edge_symm _ _ both.2⟩)
    · exact Or.inr (Or.inl ⟨both.1, problem.edge_symm _ _ both.2⟩)
  edge_irrefl := fun _ both => both.1 rfl
  edge_vertices := by
    rintro u v ⟨_, u_ne_k, _, kinds⟩
    refine Finset.mem_erase.mpr ⟨u_ne_k, ?_⟩
    rcases kinds with plain | both | both
    · exact problem.edge_vertices _ _ plain
    · exact both.1 ▸ problem.edge_vertices _ _ edge_h_k
    · exact problem.edge_vertices _ _ both.2
  relation := fun u v => if u = h then (if v = h then ∅ else merged_side problem h k name v)
    else if v = h then (merged_side problem h k name u).image Prod.swap else problem.relation u v
  relation_symm := by
    intro u v a b
    by_cases u_is_h : u = h
    · by_cases v_is_h : v = h
      · simp [u_is_h, v_is_h]
      · simp only [u_is_h, v_is_h, ite_true, ite_false, Finset.mem_image, Prod.exists,
          Prod.swap_prod_mk, Prod.mk.injEq]
        constructor
        · intro member
          exact ⟨a, b, member, rfl, rfl⟩
        · rintro ⟨_, _, member, rfl, rfl⟩
          exact member
    · by_cases v_is_h : v = h
      · simp only [u_is_h, v_is_h, ite_true, ite_false, Finset.mem_image, Prod.exists,
          Prod.swap_prod_mk, Prod.mk.injEq]
        constructor
        · rintro ⟨_, _, member, rfl, rfl⟩
          exact member
        · intro member
          exact ⟨b, a, member, rfl, rfl⟩
      · simp only [u_is_h, v_is_h, ite_false]
        exact problem.relation_symm u v a b

def is_rule_three_step (problem reduced : bct) : Prop :=
  ∃ h k name, ∃ _ : h ∉ problem.originals, ∃ k_hidden : k ∉ problem.originals,
    ∃ edge_h_k : problem.edge h k, Set.InjOn name (allowed_pairs problem h k) ∧
      reduced = rule_three problem h k name k_hidden edge_h_k

noncomputable def merge_candidate (h k : ℕ) (name : ℕ × ℕ → ℕ) (candidate : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update candidate k 0) h (name (candidate h, candidate k))

theorem merged_side_member (problem : bct) (h k : ℕ) (name : ℕ × ℕ → ℕ)
    (injective : Set.InjOn name (allowed_pairs problem h k)) (z : ℕ) (pair : ℕ × ℕ)
    (pair_mem : pair ∈ allowed_pairs problem h k) (c : ℕ) :
    (name pair, c) ∈ merged_side problem h k name z ↔ c ∈ problem.domain z ∧
      (problem.edge h z → (pair.1, c) ∈ problem.relation h z) ∧
      (problem.edge k z → (pair.2, c) ∈ problem.relation k z) := by
  simp only [merged_side, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨first, second, value, ⟨⟨other_mem, value_mem⟩, allowed_h, allowed_k⟩, same_name, rfl⟩
    have same_pair := injective other_mem pair_mem same_name
    subst same_pair
    exact ⟨value_mem, allowed_h, allowed_k⟩
  · rintro ⟨value_mem, allowed_h, allowed_k⟩
    exact ⟨pair.1, pair.2, c, ⟨⟨pair_mem, value_mem⟩, allowed_h, allowed_k⟩, rfl, rfl⟩

theorem rule_three_extensions (problem : bct) (h k : ℕ) (name : ℕ × ℕ → ℕ)
    (h_hidden : h ∉ problem.originals) (k_hidden : k ∉ problem.originals)
    (edge_h_k : problem.edge h k) (injective : Set.InjOn name (allowed_pairs problem h k))
    (tuple : ℕ → ℕ) :
    extensions (rule_three problem h k name k_hidden edge_h_k) tuple =
      merge_candidate h k name '' extensions problem tuple := by
  have h_ne_k : h ≠ k := edge_ne problem h k edge_h_k
  have h_vertex : h ∈ problem.vertices := problem.edge_vertices h k edge_h_k
  have k_vertex : k ∈ problem.vertices := edge_vertices_right problem h k edge_h_k
  ext merged
  constructor
  · rintro ⟨⟨inside, outside, holds⟩, agrees⟩
    have at_h := inside h (Finset.mem_erase.mpr ⟨h_ne_k, h_vertex⟩)
    simp only [rule_three, ite_true, Finset.mem_image] at at_h
    obtain ⟨pair, pair_mem, pair_name⟩ := at_h
    have pair_parts := pair_mem
    simp only [allowed_pairs, Finset.mem_filter, Finset.mem_product] at pair_parts
    obtain ⟨⟨first_mem, second_mem⟩, pair_allowed⟩ := pair_parts
    have at_k : merged k = 0 := outside k (by simp [rule_three])
    have side : ∀ v, v ≠ h → v ≠ k → (problem.edge h v ∨ problem.edge k v) →
        (problem.edge h v → (pair.1, merged v) ∈ problem.relation h v) ∧
          (problem.edge k v → (pair.2, merged v) ∈ problem.relation k v) := by
      intro v v_ne_h v_ne_k either
      have new_edge : (rule_three problem h k name k_hidden edge_h_k).edge h v := by
        refine ⟨v_ne_h.symm, h_ne_k, v_ne_k, ?_⟩
        rcases either with plain | plain
        · exact Or.inl plain
        · exact Or.inr (Or.inl ⟨rfl, plain⟩)
      have stated := holds h v new_edge
      simp only [rule_three, ite_true, v_ne_h, ite_false] at stated
      rw [← pair_name] at stated
      exact ((merged_side_member problem h k name injective v pair pair_mem _).mp stated).2
    have plain : ∀ u v, u ≠ h → u ≠ k → v ≠ h → v ≠ k → problem.edge u v →
        (merged u, merged v) ∈ problem.relation u v := by
      intro u v u_ne_h u_ne_k v_ne_h v_ne_k edge_u_v
      have stated := holds u v ⟨edge_ne problem u v edge_u_v, u_ne_k, v_ne_k, Or.inl edge_u_v⟩
      simpa [rule_three, u_ne_h, v_ne_h] using stated
    let restored := Function.update (Function.update merged h pair.1) k pair.2
    have restored_k : restored k = pair.2 := by simp [restored]
    have restored_h : restored h = pair.1 := by simp [restored, Function.update_of_ne h_ne_k]
    have restored_other : ∀ x, x ≠ h → x ≠ k → restored x = merged x := by
      intro x x_ne_h x_ne_k
      simp [restored, Function.update_of_ne x_ne_k, Function.update_of_ne x_ne_h]
    have from_side : ∀ u v, (u = h ∨ u = k) → problem.edge u v →
        (restored u, restored v) ∈ problem.relation u v := by
      intro u v u_special edge_u_v
      rcases u_special with rfl | rfl
      · by_cases v_is_k : v = k
        · subst v_is_k
          rw [restored_h, restored_k]
          exact pair_allowed
        · have v_ne_u : v ≠ u := (edge_ne problem u v edge_u_v).symm
          rw [restored_h, restored_other v v_ne_u v_is_k]
          exact (side v v_ne_u v_is_k (Or.inl edge_u_v)).1 edge_u_v
      · by_cases v_is_h : v = h
        · subst v_is_h
          rw [restored_h, restored_k]
          exact (problem.relation_symm _ _ _ _).mp pair_allowed
        · have v_ne_u : v ≠ u := (edge_ne problem u v edge_u_v).symm
          rw [restored_k, restored_other v v_is_h v_ne_u]
          exact (side v v_is_h v_ne_u (Or.inr edge_u_v)).2 edge_u_v
    refine ⟨restored, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro x x_vertex
      by_cases x_is_k : x = k
      · subst x_is_k
        rw [restored_k]
        exact second_mem
      · by_cases x_is_h : x = h
        · subst x_is_h
          rw [restored_h]
          exact first_mem
        · rw [restored_other x x_is_h x_is_k]
          have stated := inside x (Finset.mem_erase.mpr ⟨x_is_k, x_vertex⟩)
          simpa [rule_three, x_is_h] using stated
    · intro x x_out
      have x_ne_h : x ≠ h := fun same => x_out (same ▸ h_vertex)
      have x_ne_k : x ≠ k := fun same => x_out (same ▸ k_vertex)
      rw [restored_other x x_ne_h x_ne_k]
      exact outside x (by simp [rule_three, x_out])
    · intro u v edge_u_v
      by_cases u_special : u = h ∨ u = k
      · exact from_side u v u_special edge_u_v
      · by_cases v_special : v = h ∨ v = k
        · exact (problem.relation_symm _ _ _ _).mp
            (from_side v u v_special (problem.edge_symm _ _ edge_u_v))
        · push Not at u_special v_special
          rw [restored_other u u_special.1 u_special.2, restored_other v v_special.1 v_special.2]
          exact plain u v u_special.1 u_special.2 v_special.1 v_special.2 edge_u_v
    · intro x x_original
      rw [restored_other x (original_ne_hidden h_hidden x_original)
        (original_ne_hidden k_hidden x_original)]
      exact agrees x x_original
    · funext x
      unfold merge_candidate
      by_cases x_is_h : x = h
      · subst x_is_h
        rw [Function.update_self, restored_h, restored_k]
        exact pair_name
      · rw [Function.update_of_ne x_is_h]
        by_cases x_is_k : x = k
        · subst x_is_k
          rw [Function.update_self, at_k]
        · rw [Function.update_of_ne x_is_k]
          exact restored_other x x_is_h x_is_k
  · rintro ⟨candidate, ⟨⟨inside, outside, holds⟩, agrees⟩, rfl⟩
    have pair_mem : (candidate h, candidate k) ∈ allowed_pairs problem h k := by
      simp only [allowed_pairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨inside h h_vertex, inside k k_vertex⟩, holds h k edge_h_k⟩
    have merged_h : merge_candidate h k name candidate h = name (candidate h, candidate k) := by
      simp [merge_candidate]
    have merged_k : merge_candidate h k name candidate k = 0 := by
      simp [merge_candidate, Function.update_of_ne h_ne_k.symm]
    have merged_other : ∀ x, x ≠ h → x ≠ k → merge_candidate h k name candidate x = candidate x := by
      intro x x_ne_h x_ne_k
      simp [merge_candidate, Function.update_of_ne x_ne_h, Function.update_of_ne x_ne_k]
    have from_h : ∀ v, v ≠ h → v ≠ k → v ∈ problem.vertices →
        (merge_candidate h k name candidate h, merge_candidate h k name candidate v) ∈
          merged_side problem h k name v := by
      intro v v_ne_h v_ne_k v_vertex
      rw [merged_h, merged_other v v_ne_h v_ne_k]
      exact (merged_side_member problem h k name injective v _ pair_mem _).mpr
        ⟨inside v v_vertex, fun edge_h_v => holds h v edge_h_v, fun edge_k_v => holds k v edge_k_v⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x x_vertex
      obtain ⟨x_ne_k, x_old⟩ := Finset.mem_erase.mp x_vertex
      by_cases x_is_h : x = h
      · subst x_is_h
        rw [merged_h]
        simp only [rule_three, ite_true]
        exact Finset.mem_image_of_mem name pair_mem
      · rw [merged_other x x_is_h x_ne_k]
        simpa [rule_three, x_is_h] using inside x x_old
    · intro x x_out
      by_cases x_is_k : x = k
      · subst x_is_k
        exact merged_k
      · have x_not_old : x ∉ problem.vertices := fun x_old =>
          x_out (Finset.mem_erase.mpr ⟨x_is_k, x_old⟩)
        have x_ne_h : x ≠ h := fun same => x_not_old (same ▸ h_vertex)
        rw [merged_other x x_ne_h x_is_k]
        exact outside x x_not_old
    · intro u v new_edge
      have u_vertex := (rule_three problem h k name k_hidden edge_h_k).edge_vertices u v new_edge
      have v_vertex := edge_vertices_right (rule_three problem h k name k_hidden edge_h_k) u v new_edge
      obtain ⟨u_ne_v, u_ne_k, v_ne_k, kinds⟩ := new_edge
      by_cases u_is_h : u = h
      · subst u_is_h
        have v_ne_u : v ≠ u := u_ne_v.symm
        simp only [rule_three, ite_true, v_ne_u, ite_false]
        exact from_h v v_ne_u v_ne_k (Finset.mem_of_mem_erase v_vertex)
      · by_cases v_is_h : v = h
        · subst v_is_h
          simp only [rule_three, u_is_h, ite_true, ite_false]
          exact Finset.mem_image.mpr ⟨_, from_h u u_is_h u_ne_k (Finset.mem_of_mem_erase u_vertex), rfl⟩
        · simp only [rule_three, u_is_h, v_is_h, ite_false]
          rw [merged_other u u_is_h u_ne_k, merged_other v v_is_h v_ne_k]
          rcases kinds with plain | both | both
          · exact holds u v plain
          · exact absurd both.1 u_is_h
          · exact absurd both.1 v_is_h
    · intro x x_original
      rw [merged_other x (original_ne_hidden h_hidden x_original)
        (original_ne_hidden k_hidden x_original)]
      exact agrees x x_original

theorem merge_candidate_injective (problem : bct) (h k : ℕ) (name : ℕ × ℕ → ℕ)
    (edge_h_k : problem.edge h k) (injective : Set.InjOn name (allowed_pairs problem h k))
    (tuple : ℕ → ℕ) : Set.InjOn (merge_candidate h k name) (extensions problem tuple) := by
  have h_ne_k : h ≠ k := edge_ne problem h k edge_h_k
  have h_vertex : h ∈ problem.vertices := problem.edge_vertices h k edge_h_k
  have k_vertex : k ∈ problem.vertices := edge_vertices_right problem h k edge_h_k
  have pair_member : ∀ candidate ∈ extensions problem tuple,
      (candidate h, candidate k) ∈ allowed_pairs problem h k := by
    intro candidate member
    simp only [allowed_pairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨member.1.1 h h_vertex, member.1.1 k k_vertex⟩, member.1.2.2 h k edge_h_k⟩
  intro first first_mem second second_mem same
  have same_pair : (first h, first k) = (second h, second k) := by
    apply injective (pair_member first first_mem) (pair_member second second_mem)
    have at_h := congrFun same h
    simpa [merge_candidate] using at_h
  simp only [Prod.mk.injEq] at same_pair
  funext x
  by_cases x_is_h : x = h
  · rw [x_is_h]
    exact same_pair.1
  · by_cases x_is_k : x = k
    · rw [x_is_k]
      exact same_pair.2
    · have at_x := congrFun same x
      simpa [merge_candidate, Function.update_of_ne x_is_h, Function.update_of_ne x_is_k] using at_x

theorem rule_three_step_counts (problem reduced : bct) (step : is_rule_three_step problem reduced)
    (tuple : ℕ → ℕ) : extension_count reduced tuple = extension_count problem tuple ∧
      (in_relation reduced tuple ↔ in_relation problem tuple) := by
  obtain ⟨h, k, name, h_hidden, k_hidden, edge_h_k, injective, rfl⟩ := step
  have image := rule_three_extensions problem h k name h_hidden k_hidden edge_h_k injective tuple
  constructor
  · unfold extension_count
    rw [image]
    exact (merge_candidate_injective problem h k name edge_h_k injective tuple).ncard_image
  · unfold in_relation
    rw [image]
    exact Set.image_nonempty

theorem rule_three_empty_domain (problem : bct) (h k : ℕ) (edge_h_k : problem.edge h k)
    (empty : allowed_pairs problem h k = ∅) (candidate : ℕ → ℕ) :
    ¬ is_solution problem candidate := by
  rintro ⟨inside, _, holds⟩
  have member : (candidate h, candidate k) ∈ allowed_pairs problem h k := by
    simp only [allowed_pairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨inside h (problem.edge_vertices h k edge_h_k),
      inside k (edge_vertices_right problem h k edge_h_k)⟩, holds h k edge_h_k⟩
  rw [empty] at member
  exact absurd member (Finset.notMem_empty _)

end rules
end parsimony
