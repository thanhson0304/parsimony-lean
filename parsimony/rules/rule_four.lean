import parsimony.rules.rule_three

namespace parsimony
namespace rules

open scoped Classical

def value_fits (problem : bct) (h a : ℕ) (neighbours : ℕ → ℕ) : Prop :=
  ∀ y, problem.edge h y → (a, neighbours y) ∈ problem.relation h y

def box_fits (problem : bct) (h : ℕ) (box : Finset (ℕ × ℕ)) (neighbours : ℕ → ℕ) : Prop :=
  ∀ y, problem.edge h y → (y, neighbours y) ∈ box

def is_current (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ) : Prop :=
  ∀ y, problem.edge h y → neighbours y ∈ problem.domain y

noncomputable def old_value_count (problem : bct) (h : ℕ) (neighbours : ℕ → ℕ) : ℕ :=
  ((problem.domain h).filter fun a => value_fits problem h a neighbours).card

noncomputable def box_count (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (neighbours : ℕ → ℕ) : ℕ :=
  (table.filter fun box => box_fits problem h box neighbours).card

def is_valid_table (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ))) : Prop :=
  ∀ neighbours, is_current problem h neighbours →
    ((∃ a ∈ problem.domain h, value_fits problem h a neighbours) ↔
      ∃ box ∈ table, box_fits problem h box neighbours)

def is_rest (problem : bct) (h : ℕ) (tuple rest : ℕ → ℕ) : Prop :=
  rest h = 0 ∧ (∀ x ∈ problem.vertices, x ≠ h → rest x ∈ problem.domain x) ∧
  (∀ x, x ∉ problem.vertices → rest x = 0) ∧
  (∀ x y, problem.edge x y → x ≠ h → y ≠ h → (rest x, rest y) ∈ problem.relation x y) ∧
  ∀ x ∈ problem.originals, rest x = tuple x

theorem rests_finite (problem : bct) (h : ℕ) (tuple : ℕ → ℕ) :
    {rest | is_rest problem h tuple rest}.Finite := by
  refine (bounded_functions_finite problem.vertices
    (fun x => if x = h then {0} else problem.domain x)).subset ?_
  rintro rest ⟨at_h, inside, outside, _⟩
  refine ⟨fun x x_vertex => ?_, outside⟩
  by_cases x_is_h : x = h
  · simp [x_is_h, at_h]
  · simpa [x_is_h] using inside x x_vertex x_is_h

noncomputable def rests (problem : bct) (h : ℕ) (tuple : ℕ → ℕ) : Finset (ℕ → ℕ) :=
  (rests_finite problem h tuple).toFinset

theorem mem_rests (problem : bct) (h : ℕ) (tuple rest : ℕ → ℕ) :
    rest ∈ rests problem h tuple ↔ is_rest problem h tuple rest := by
  simp [rests]

theorem rest_is_current (problem : bct) (h : ℕ) (tuple rest : ℕ → ℕ)
    (is_rest_rest : is_rest problem h tuple rest) : is_current problem h rest :=
  fun y edge_h_y => is_rest_rest.2.1 y (edge_vertices_right problem h y edge_h_y)
    (edge_ne problem h y edge_h_y).symm

theorem forget_is_rest (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (tuple candidate : ℕ → ℕ)
    (member : candidate ∈ extensions problem tuple) :
    is_rest problem h tuple (Function.update candidate h 0) := by
  obtain ⟨⟨inside, outside, holds⟩, agrees⟩ := member
  refine ⟨Function.update_self .., fun x x_vertex x_ne_h => ?_, fun x x_out => ?_,
    fun x y edge_x_y x_ne_h y_ne_h => ?_, fun x x_original => ?_⟩
  · rw [Function.update_of_ne x_ne_h]
    exact inside x x_vertex
  · have x_ne_h : x ≠ h := fun same => x_out (same ▸ h_vertex)
    rw [Function.update_of_ne x_ne_h]
    exact outside x x_out
  · rw [Function.update_of_ne x_ne_h, Function.update_of_ne y_ne_h]
    exact holds x y edge_x_y
  · rw [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
    exact agrees x x_original

theorem complete_rest (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (tuple rest : ℕ → ℕ)
    (is_rest_rest : is_rest problem h tuple rest) (a : ℕ) :
    Function.update rest h a ∈ extensions problem tuple ↔
      a ∈ problem.domain h ∧ value_fits problem h a rest := by
  obtain ⟨_, inside, outside, holds, agrees⟩ := is_rest_rest
  constructor
  · rintro ⟨⟨new_inside, _, new_holds⟩, _⟩
    refine ⟨by simpa using new_inside h h_vertex, fun y edge_h_y => ?_⟩
    have stated := new_holds h y edge_h_y
    rwa [Function.update_self, Function.update_of_ne (edge_ne problem h y edge_h_y).symm] at stated
  · rintro ⟨a_mem, fits⟩
    refine ⟨⟨fun x x_vertex => ?_, fun x x_out => ?_, fun u v edge_u_v => ?_⟩, fun x x_original => ?_⟩
    · by_cases x_is_h : x = h
      · subst x_is_h
        simpa using a_mem
      · rw [Function.update_of_ne x_is_h]
        exact inside x x_vertex x_is_h
    · have x_ne_h : x ≠ h := fun same => x_out (same ▸ h_vertex)
      rw [Function.update_of_ne x_ne_h]
      exact outside x x_out
    · by_cases u_is_h : u = h
      · subst u_is_h
        rw [Function.update_self, Function.update_of_ne (edge_ne problem u v edge_u_v).symm]
        exact fits v edge_u_v
      · by_cases v_is_h : v = h
        · subst v_is_h
          rw [Function.update_self, Function.update_of_ne u_is_h]
          exact (problem.relation_symm _ _ _ _).mp (fits u (problem.edge_symm _ _ edge_u_v))
        · rw [Function.update_of_ne u_is_h, Function.update_of_ne v_is_h]
          exact holds u v edge_u_v u_is_h v_is_h
    · rw [Function.update_of_ne (original_ne_hidden h_hidden x_original)]
      exact agrees x x_original

theorem update_injective (rest : ℕ → ℕ) (h : ℕ) :
    Function.Injective fun a => Function.update rest h a := by
  intro first second same
  have at_h := congrFun same h
  simpa using at_h

theorem extension_count_eq_sum (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (tuple : ℕ → ℕ) :
    extension_count problem tuple = ∑ rest ∈ rests problem h tuple, old_value_count problem h rest := by
  unfold extension_count
  rw [Set.ncard_eq_toFinset_card _ (extensions_finite problem tuple)]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun candidate => Function.update candidate h 0)
    (t := rests problem h tuple)]
  · refine Finset.sum_congr rfl fun rest rest_mem => ?_
    have is_rest_rest := (mem_rests problem h tuple rest).mp rest_mem
    have same : (extensions_finite problem tuple).toFinset.filter
        (fun candidate => Function.update candidate h 0 = rest) =
        ((problem.domain h).filter fun a => value_fits problem h a rest).image
          (fun a => Function.update rest h a) := by
      ext candidate
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨member, forgot⟩
        refine ⟨candidate h, ?_, ?_⟩
        · have restored : Function.update rest h (candidate h) = candidate := by
            rw [← forgot]
            simp
          rw [← complete_rest problem h h_vertex h_hidden tuple rest is_rest_rest, restored]
          exact member
        · rw [← forgot]
          simp
      · rintro ⟨a, fits, rfl⟩
        refine ⟨(complete_rest problem h h_vertex h_hidden tuple rest is_rest_rest a).mpr fits, ?_⟩
        rw [Function.update_idem]
        rw [← is_rest_rest.1]
        simp
    rw [same, Finset.card_image_of_injective _ (update_injective rest h)]
    rfl
  · intro candidate member
    have in_set : candidate ∈ extensions problem tuple := by simpa using member
    exact Finset.mem_coe.mpr ((mem_rests problem h tuple _).mpr
      (forget_is_rest problem h h_vertex h_hidden tuple candidate in_set))

noncomputable def box_side (table : Finset (Finset (ℕ × ℕ))) (name : Finset (ℕ × ℕ) → ℕ) (y : ℕ) :
    Finset (ℕ × ℕ) :=
  table.biUnion fun box => (box.filter fun literal => literal.1 = y).image
    fun literal => (name box, literal.2)

theorem box_side_member (table : Finset (Finset (ℕ × ℕ))) (name : Finset (ℕ × ℕ) → ℕ)
    (injective : Set.InjOn name table) (y : ℕ) (box : Finset (ℕ × ℕ)) (box_mem : box ∈ table) (b : ℕ) :
    (name box, b) ∈ box_side table name y ↔ (y, b) ∈ box := by
  simp only [box_side, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨other, other_mem, z, c, ⟨literal_mem, rfl⟩, same_name, rfl⟩
    have same_box := injective other_mem box_mem same_name
    subst same_box
    exact literal_mem
  · intro literal_mem
    exact ⟨box, box_mem, y, b, ⟨literal_mem, rfl⟩, rfl, rfl⟩

noncomputable def rule_four (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) : bct where
  vertices := problem.vertices
  originals := problem.originals
  originals_subset := problem.originals_subset
  domain := fun x => if x = h then table.image name else problem.domain x
  edge := problem.edge
  edge_symm := problem.edge_symm
  edge_irrefl := problem.edge_irrefl
  edge_vertices := problem.edge_vertices
  relation := fun u v => if u = h then (if v = h then ∅ else box_side table name v)
    else if v = h then (box_side table name u).image Prod.swap else problem.relation u v
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

theorem rule_four_rests (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (tuple : ℕ → ℕ) :
    rests (rule_four problem h table name) h tuple = rests problem h tuple := by
  ext rest
  rw [mem_rests, mem_rests]
  constructor
  · rintro ⟨at_h, inside, outside, holds, agrees⟩
    refine ⟨at_h, fun x x_vertex x_ne_h => ?_, outside, fun x y edge_x_y x_ne_h y_ne_h => ?_, agrees⟩
    · simpa [rule_four, x_ne_h] using inside x x_vertex x_ne_h
    · simpa [rule_four, x_ne_h, y_ne_h] using holds x y edge_x_y x_ne_h y_ne_h
  · rintro ⟨at_h, inside, outside, holds, agrees⟩
    refine ⟨at_h, fun x x_vertex x_ne_h => ?_, outside, fun x y edge_x_y x_ne_h y_ne_h => ?_, agrees⟩
    · simpa [rule_four, x_ne_h] using inside x x_vertex x_ne_h
    · simpa [rule_four, x_ne_h, y_ne_h] using holds x y edge_x_y x_ne_h y_ne_h

theorem rule_four_value_count (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (injective : Set.InjOn name table) (neighbours : ℕ → ℕ) :
    old_value_count (rule_four problem h table name) h neighbours =
      box_count problem h table neighbours := by
  have fits_iff : ∀ box ∈ table, (value_fits (rule_four problem h table name) h (name box) neighbours ↔
      box_fits problem h box neighbours) := by
    intro box box_mem
    refine forall_congr' fun y => ?_
    refine imp_congr_right fun edge_h_y => ?_
    have y_ne_h : y ≠ h := (edge_ne problem h y edge_h_y).symm
    simp only [rule_four, ite_true, y_ne_h, ite_false]
    exact box_side_member table name injective y box box_mem (neighbours y)
  unfold old_value_count box_count
  have domain_is : (rule_four problem h table name).domain h = table.image name := by
    simp [rule_four]
  rw [domain_is]
  have same : (table.image name).filter
      (fun a => value_fits (rule_four problem h table name) h a neighbours) =
      (table.filter fun box => box_fits problem h box neighbours).image name := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨box, box_mem, rfl⟩, fits⟩
      exact ⟨box, ⟨box_mem, (fits_iff box box_mem).mp fits⟩, rfl⟩
    · rintro ⟨box, ⟨box_mem, fits⟩, rfl⟩
      exact ⟨⟨box, box_mem, rfl⟩, (fits_iff box box_mem).mpr fits⟩
  rw [same]
  exact Finset.card_image_of_injOn fun first first_mem second second_mem =>
    injective (Finset.mem_filter.mp first_mem).1 (Finset.mem_filter.mp second_mem).1

theorem rule_four_count (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (injective : Set.InjOn name table) (tuple : ℕ → ℕ) :
    extension_count (rule_four problem h table name) tuple =
      ∑ rest ∈ rests problem h tuple, box_count problem h table rest := by
  rw [extension_count_eq_sum (rule_four problem h table name) h h_vertex h_hidden tuple,
    rule_four_rests]
  exact Finset.sum_congr rfl fun rest _ => rule_four_value_count problem h table name injective rest

theorem count_pos_iff (problem : bct) (h : ℕ) (table : Finset (Finset (ℕ × ℕ)))
    (valid : is_valid_table problem h table) (neighbours : ℕ → ℕ)
    (current : is_current problem h neighbours) :
    0 < box_count problem h table neighbours ↔ 0 < old_value_count problem h neighbours := by
  unfold box_count old_value_count
  rw [Finset.card_pos, Finset.card_pos, Finset.filter_nonempty_iff, Finset.filter_nonempty_iff]
  exact (valid neighbours current).symm

theorem rule_four_relation (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (injective : Set.InjOn name table)
    (valid : is_valid_table problem h table) (tuple : ℕ → ℕ) :
    in_relation (rule_four problem h table name) tuple ↔ in_relation problem tuple := by
  rw [← extension_count_pos_iff, ← extension_count_pos_iff,
    rule_four_count problem h h_vertex h_hidden table name injective,
    extension_count_eq_sum problem h h_vertex h_hidden]
  rw [Finset.sum_pos_iff, Finset.sum_pos_iff]
  refine exists_congr fun rest => and_congr_right fun rest_mem => ?_
  exact count_pos_iff problem h table valid rest
    (rest_is_current problem h tuple rest ((mem_rests problem h tuple rest).mp rest_mem))

theorem rule_four_count_le (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (injective : Set.InjOn name table) (tuple : ℕ → ℕ)
    (pointwise : ∀ neighbours, is_current problem h neighbours →
      box_count problem h table neighbours ≤ old_value_count problem h neighbours) :
    extension_count (rule_four problem h table name) tuple ≤ extension_count problem tuple := by
  rw [rule_four_count problem h h_vertex h_hidden table name injective,
    extension_count_eq_sum problem h h_vertex h_hidden]
  exact Finset.sum_le_sum fun rest rest_mem => pointwise rest
    (rest_is_current problem h tuple rest ((mem_rests problem h tuple rest).mp rest_mem))

theorem unique_sum_at_solution (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (table : Finset (Finset (ℕ × ℕ)))
    (valid : is_valid_table problem h table) (unique : has_unique_extension problem)
    (tuple candidate : ℕ → ℕ) (member : candidate ∈ extensions problem tuple) :
    ∑ rest ∈ rests problem h tuple, box_count problem h table rest =
      box_count problem h table candidate := by
  have old_sum := extension_count_eq_sum problem h h_vertex h_hidden tuple
  rw [unique tuple ⟨candidate, member⟩] at old_sum
  have rest_member : Function.update candidate h 0 ∈ rests problem h tuple :=
    (mem_rests problem h tuple _).mpr (forget_is_rest problem h h_vertex h_hidden tuple candidate member)
  have same_neighbours : ∀ y, problem.edge h y → Function.update candidate h 0 y = candidate y :=
    fun y edge_h_y => Function.update_of_ne (edge_ne problem h y edge_h_y).symm 0 candidate
  have at_candidate : box_count problem h table (Function.update candidate h 0) =
      box_count problem h table candidate := by
    unfold box_count
    congr 1
    refine Finset.filter_congr fun box _ => forall_congr' fun y => imp_congr_right fun edge_h_y => ?_
    rw [same_neighbours y edge_h_y]
  have positive : 0 < old_value_count problem h (Function.update candidate h 0) := by
    unfold old_value_count
    rw [Finset.card_pos, Finset.filter_nonempty_iff]
    refine ⟨candidate h, member.1.1 h h_vertex, fun y edge_h_y => ?_⟩
    rw [same_neighbours y edge_h_y]
    exact member.1.2.2 h y edge_h_y
  rw [Finset.sum_eq_single_of_mem _ rest_member, at_candidate]
  intro other other_mem other_ne
  have old_zero : old_value_count problem h other = 0 := by
    by_contra nonzero
    have pair_le := Finset.add_le_sum (f := fun rest => old_value_count problem h rest)
      (fun _ _ => Nat.zero_le _) rest_member other_mem other_ne.symm
    omega
  by_contra nonzero
  have current := rest_is_current problem h tuple other ((mem_rests problem h tuple other).mp other_mem)
  have back := (count_pos_iff problem h table valid other current).mp (Nat.pos_of_ne_zero nonzero)
  omega

theorem rule_four_unique_iff (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (injective : Set.InjOn name table)
    (valid : is_valid_table problem h table) (unique : has_unique_extension problem) :
    has_unique_extension (rule_four problem h table name) ↔
      ∀ candidate, is_solution problem candidate → box_count problem h table candidate = 1 := by
  constructor
  · intro new_unique candidate solution
    have member : candidate ∈ extensions problem candidate := ⟨solution, fun _ _ => rfl⟩
    have relation := (rule_four_relation problem h h_vertex h_hidden table name injective valid
      candidate).mpr ⟨candidate, member⟩
    have counted := new_unique candidate relation
    rw [rule_four_count problem h h_vertex h_hidden table name injective,
      unique_sum_at_solution problem h h_vertex h_hidden table valid unique candidate candidate member]
      at counted
    exact counted
  · intro covered_once tuple new_relation
    obtain ⟨candidate, member⟩ := (rule_four_relation problem h h_vertex h_hidden table name injective
      valid tuple).mp new_relation
    rw [rule_four_count problem h h_vertex h_hidden table name injective,
      unique_sum_at_solution problem h h_vertex h_hidden table valid unique tuple candidate member]
    exact covered_once candidate member.1

theorem rule_four_covered_once (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (h_hidden : h ∉ problem.originals) (table : Finset (Finset (ℕ × ℕ)))
    (name : Finset (ℕ × ℕ) → ℕ) (injective : Set.InjOn name table)
    (valid : is_valid_table problem h table) (unique : has_unique_extension problem)
    (covered_once : ∀ neighbours, is_current problem h neighbours →
      (∃ a ∈ problem.domain h, value_fits problem h a neighbours) →
        box_count problem h table neighbours = 1) :
    has_unique_extension (rule_four problem h table name) := by
  rw [rule_four_unique_iff problem h h_vertex h_hidden table name injective valid unique]
  intro candidate solution
  refine covered_once candidate (fun y edge_h_y =>
    solution.1 y (edge_vertices_right problem h y edge_h_y)) ?_
  exact ⟨candidate h, solution.1 h h_vertex, fun y edge_h_y => solution.2.2 h y edge_h_y⟩

theorem rule_four_empty_domain (problem : bct) (h : ℕ) (h_vertex : h ∈ problem.vertices)
    (valid : is_valid_table problem h ∅) (candidate : ℕ → ℕ) : ¬ is_solution problem candidate := by
  intro solution
  obtain ⟨box, box_mem, _⟩ := (valid candidate (fun y edge_h_y =>
    solution.1 y (edge_vertices_right problem h y edge_h_y))).mp
    ⟨candidate h, solution.1 h h_vertex, fun y edge_h_y => solution.2.2 h y edge_h_y⟩
  exact absurd box_mem (Finset.notMem_empty _)

theorem isolated_vertex_table (problem : bct) (h : ℕ) (isolated : ∀ y, ¬ problem.edge h y)
    (domain_nonempty : (problem.domain h).Nonempty) (table : Finset (Finset (ℕ × ℕ)))
    (over_neighbours : ∀ box ∈ table, ∀ literal ∈ box, problem.edge h literal.1)
    (valid : is_valid_table problem h table) : table = {∅} := by
  have empty_boxes : ∀ box ∈ table, box = ∅ := by
    intro box box_mem
    refine Finset.eq_empty_of_forall_notMem fun literal literal_mem => ?_
    exact isolated literal.1 (over_neighbours box box_mem literal literal_mem)
  obtain ⟨a, a_mem⟩ := domain_nonempty
  obtain ⟨box, box_mem, _⟩ := (valid (fun _ => 0) (fun y edge_h_y => absurd edge_h_y (isolated y))).mp
    ⟨a, a_mem, fun y edge_h_y => absurd edge_h_y (isolated y)⟩
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, empty_boxes⟩
  rw [← empty_boxes box box_mem]
  exact box_mem

end rules
end parsimony
