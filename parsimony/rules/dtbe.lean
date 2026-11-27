import parsimony.rules.cct_construction

namespace parsimony
namespace rules

open scoped Classical

structure layered_diagram where
  layer_count : ℕ
  layer_pos : 0 < layer_count
  symbols : ℕ → Finset ℕ
  nodes : ℕ → Finset ℕ
  arcs : ℕ → Finset ℕ
  source : ℕ → ℕ → ℕ
  label : ℕ → ℕ → ℕ
  target : ℕ → ℕ → ℕ

def original_of (layer : ℕ) : ℕ := 3 * layer

def arc_of (layer : ℕ) : ℕ := 3 * layer + 1

def node_of (layer : ℕ) : ℕ := 3 * layer + 2

def is_link (layer_count u v : ℕ) : Prop :=
  ∃ layer < layer_count, u = arc_of layer ∧
    (v = original_of layer ∨ v = node_of layer ∨ v = node_of (layer + 1))

noncomputable def link (diagram : layered_diagram) (u v : ℕ) : Finset (ℕ × ℕ) :=
  if v = original_of (u / 3) then (diagram.arcs (u / 3)).image fun e => (e, diagram.label (u / 3) e)
  else if v = node_of (u / 3) then
    (diagram.arcs (u / 3)).image fun e => (e, diagram.source (u / 3) e)
  else if v = node_of (u / 3 + 1) then
    (diagram.arcs (u / 3)).image fun e => (e, diagram.target (u / 3) e)
  else ∅

noncomputable def dtbe (diagram : layered_diagram) : bct where
  vertices := (Finset.range diagram.layer_count).image original_of ∪
    (Finset.range diagram.layer_count).image arc_of ∪
    (Finset.range (diagram.layer_count + 1)).image node_of
  originals := (Finset.range diagram.layer_count).image original_of
  originals_subset := fun _ member => Finset.mem_union_left _ (Finset.mem_union_left _ member)
  domain := fun x => if x % 3 = 0 then diagram.symbols (x / 3)
    else if x % 3 = 1 then diagram.arcs (x / 3) else diagram.nodes (x / 3)
  edge := fun u v => is_link diagram.layer_count u v ∨ is_link diagram.layer_count v u
  edge_symm := fun _ _ either => either.symm
  edge_irrefl := by
    rintro x (⟨layer, _, at_arc, at_other⟩ | ⟨layer, _, at_arc, at_other⟩) <;>
    · simp only [arc_of, original_of, node_of] at at_arc at_other
      omega
  edge_vertices := by
    rintro u v (⟨layer, layer_lt, rfl, _⟩ | ⟨layer, layer_lt, _, at_other⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_range.mpr layer_lt)))
    · rcases at_other with rfl | rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_range.mpr layer_lt)))
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
      · exact Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
  relation := fun u v => if u % 3 = 1 ∧ v % 3 ≠ 1 then link diagram u v
    else if v % 3 = 1 ∧ u % 3 ≠ 1 then (link diagram v u).image Prod.swap else ∅
  relation_symm := by
    intro u v a b
    by_cases forward : u % 3 = 1 ∧ v % 3 ≠ 1
    · simp only [forward, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true,
        and_self, Finset.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      constructor
      · intro member
        exact ⟨a, b, member, rfl, rfl⟩
      · rintro ⟨_, _, member, rfl, rfl⟩
        exact member
    · by_cases backward : v % 3 = 1 ∧ u % 3 ≠ 1
      · simp only [backward, ite_true, ite_false, ne_eq, not_true_eq_false,
          not_false_eq_true, and_self, Finset.mem_image, Prod.exists, Prod.swap_prod_mk,
          Prod.mk.injEq]
        constructor
        · rintro ⟨_, _, member, rfl, rfl⟩
          exact member
        · intro member
          exact ⟨b, a, member, rfl, rfl⟩
      · simp only [forward, backward, ite_false, Finset.notMem_empty]

theorem arc_original_relation (diagram : layered_diagram) (layer e b : ℕ) :
    (e, b) ∈ (dtbe diagram).relation (arc_of layer) (original_of layer) ↔
      e ∈ diagram.arcs layer ∧ b = diagram.label layer e := by
  have first : arc_of layer % 3 = 1 := by unfold arc_of; omega
  have second : original_of layer % 3 ≠ 1 := by unfold original_of; omega
  have quotient : arc_of layer / 3 = layer := by unfold arc_of; omega
  simp only [dtbe, first, second, ne_eq, not_false_eq_true, and_self, ite_true, link, quotient,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨other, other_mem, rfl, rfl⟩
    exact ⟨other_mem, rfl⟩
  · rintro ⟨e_mem, rfl⟩
    exact ⟨e, e_mem, rfl, rfl⟩

theorem arc_source_relation (diagram : layered_diagram) (layer e b : ℕ) :
    (e, b) ∈ (dtbe diagram).relation (arc_of layer) (node_of layer) ↔
      e ∈ diagram.arcs layer ∧ b = diagram.source layer e := by
  have first : arc_of layer % 3 = 1 := by unfold arc_of; omega
  have second : node_of layer % 3 ≠ 1 := by unfold node_of; omega
  have quotient : arc_of layer / 3 = layer := by unfold arc_of; omega
  have not_original : node_of layer ≠ original_of layer := by unfold node_of original_of; omega
  simp only [dtbe, first, second, ne_eq, not_false_eq_true, and_self, ite_true, link, quotient,
    not_original, ite_false, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨other, other_mem, rfl, rfl⟩
    exact ⟨other_mem, rfl⟩
  · rintro ⟨e_mem, rfl⟩
    exact ⟨e, e_mem, rfl, rfl⟩

theorem arc_target_relation (diagram : layered_diagram) (layer e b : ℕ) :
    (e, b) ∈ (dtbe diagram).relation (arc_of layer) (node_of (layer + 1)) ↔
      e ∈ diagram.arcs layer ∧ b = diagram.target layer e := by
  have first : arc_of layer % 3 = 1 := by unfold arc_of; omega
  have second : node_of (layer + 1) % 3 ≠ 1 := by unfold node_of; omega
  have quotient : arc_of layer / 3 = layer := by unfold arc_of; omega
  have not_original : node_of (layer + 1) ≠ original_of layer := by unfold node_of original_of; omega
  have not_source : node_of (layer + 1) ≠ node_of layer := by unfold node_of; omega
  simp only [dtbe, first, second, ne_eq, not_false_eq_true, and_self, ite_true, link, quotient,
    not_original, not_source, ite_false, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨other, other_mem, rfl, rfl⟩
    exact ⟨other_mem, rfl⟩
  · rintro ⟨e_mem, rfl⟩
    exact ⟨e, e_mem, rfl, rfl⟩

theorem original_domain (diagram : layered_diagram) (layer : ℕ) :
    (dtbe diagram).domain (original_of layer) = diagram.symbols layer := by
  have first : original_of layer % 3 = 0 := by unfold original_of; omega
  have quotient : original_of layer / 3 = layer := by unfold original_of; omega
  simp [dtbe, first, quotient]

theorem arc_domain (diagram : layered_diagram) (layer : ℕ) :
    (dtbe diagram).domain (arc_of layer) = diagram.arcs layer := by
  have first : arc_of layer % 3 = 1 := by unfold arc_of; omega
  have quotient : arc_of layer / 3 = layer := by unfold arc_of; omega
  simp [dtbe, first, quotient]

theorem node_domain (diagram : layered_diagram) (layer : ℕ) :
    (dtbe diagram).domain (node_of layer) = diagram.nodes layer := by
  have first : node_of layer % 3 = 2 := by unfold node_of; omega
  have quotient : node_of layer / 3 = layer := by unfold node_of; omega
  simp [dtbe, first, quotient]

theorem mem_vertices (diagram : layered_diagram) (x : ℕ) : x ∈ (dtbe diagram).vertices ↔
    (∃ layer < diagram.layer_count, x = original_of layer) ∨
    (∃ layer < diagram.layer_count, x = arc_of layer) ∨
    ∃ layer ≤ diagram.layer_count, x = node_of layer := by
  simp only [dtbe, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ((⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_lt, rfl⟩) | ⟨layer, layer_lt, rfl⟩)
    · exact Or.inl ⟨layer, layer_lt, rfl⟩
    · exact Or.inr (Or.inl ⟨layer, layer_lt, rfl⟩)
    · exact Or.inr (Or.inr ⟨layer, by omega, rfl⟩)
  · rintro (⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_le, rfl⟩)
    · exact Or.inl (Or.inl ⟨layer, layer_lt, rfl⟩)
    · exact Or.inl (Or.inr ⟨layer, layer_lt, rfl⟩)
    · exact Or.inr ⟨layer, by omega, rfl⟩

def follows_arcs (diagram : layered_diagram) (candidate : ℕ → ℕ) : Prop :=
  ∀ layer < diagram.layer_count, candidate (arc_of layer) ∈ diagram.arcs layer ∧
    candidate (original_of layer) = diagram.label layer (candidate (arc_of layer)) ∧
    candidate (node_of layer) = diagram.source layer (candidate (arc_of layer)) ∧
    candidate (node_of (layer + 1)) = diagram.target layer (candidate (arc_of layer))

theorem dtbe_solution_iff (diagram : layered_diagram) (candidate : ℕ → ℕ) :
    is_solution (dtbe diagram) candidate ↔ follows_arcs diagram candidate ∧
      (∀ layer < diagram.layer_count, candidate (original_of layer) ∈ diagram.symbols layer) ∧
      (∀ layer ≤ diagram.layer_count, candidate (node_of layer) ∈ diagram.nodes layer) ∧
      ∀ x, x ∉ (dtbe diagram).vertices → candidate x = 0 := by
  constructor
  · rintro ⟨inside, outside, holds⟩
    refine ⟨fun layer layer_lt => ?_, fun layer layer_lt => ?_, fun layer layer_le => ?_, outside⟩
    · have with_original := (arc_original_relation diagram layer _ _).mp
        (holds (arc_of layer) (original_of layer) (Or.inl ⟨layer, layer_lt, rfl, Or.inl rfl⟩))
      have with_source := (arc_source_relation diagram layer _ _).mp
        (holds (arc_of layer) (node_of layer) (Or.inl ⟨layer, layer_lt, rfl, Or.inr (Or.inl rfl)⟩))
      have with_target := (arc_target_relation diagram layer _ _).mp
        (holds (arc_of layer) (node_of (layer + 1))
          (Or.inl ⟨layer, layer_lt, rfl, Or.inr (Or.inr rfl)⟩))
      exact ⟨with_original.1, with_original.2, with_source.2, with_target.2⟩
    · rw [← original_domain]
      exact inside _ ((mem_vertices diagram _).mpr (Or.inl ⟨layer, layer_lt, rfl⟩))
    · rw [← node_domain]
      exact inside _ ((mem_vertices diagram _).mpr (Or.inr (Or.inr ⟨layer, layer_le, rfl⟩)))
  · rintro ⟨follows, at_originals, at_nodes, outside⟩
    have linked : ∀ u v, is_link diagram.layer_count u v →
        (candidate u, candidate v) ∈ (dtbe diagram).relation u v := by
      rintro u v ⟨layer, layer_lt, rfl, rfl | rfl | rfl⟩
      · exact (arc_original_relation diagram layer _ _).mpr
          ⟨(follows layer layer_lt).1, (follows layer layer_lt).2.1⟩
      · exact (arc_source_relation diagram layer _ _).mpr
          ⟨(follows layer layer_lt).1, (follows layer layer_lt).2.2.1⟩
      · exact (arc_target_relation diagram layer _ _).mpr
          ⟨(follows layer layer_lt).1, (follows layer layer_lt).2.2.2⟩
    refine ⟨fun x x_vertex => ?_, outside, fun u v either => ?_⟩
    · rcases (mem_vertices diagram x).mp x_vertex with
        ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_le, rfl⟩
      · rw [original_domain]
        exact at_originals layer layer_lt
      · rw [arc_domain]
        exact (follows layer layer_lt).1
      · rw [node_domain]
        exact at_nodes layer layer_le
    · rcases either with forward | backward
      · exact linked u v forward
      · exact ((dtbe diagram).relation_symm _ _ _ _).mp (linked v u backward)

def is_path (diagram : layered_diagram) (path : ℕ → ℕ) : Prop :=
  (∀ layer < diagram.layer_count, path layer ∈ diagram.arcs layer ∧
    diagram.label layer (path layer) ∈ diagram.symbols layer ∧
    diagram.source layer (path layer) ∈ diagram.nodes layer ∧
    diagram.target layer (path layer) ∈ diagram.nodes (layer + 1)) ∧
  (∀ layer, layer + 1 < diagram.layer_count →
    diagram.target layer (path layer) = diagram.source (layer + 1) (path (layer + 1))) ∧
  ∀ layer, diagram.layer_count ≤ layer → path layer = 0

def paths_spelling (diagram : layered_diagram) (tuple : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {path | is_path diagram path ∧
    ∀ layer < diagram.layer_count, diagram.label layer (path layer) = tuple (original_of layer)}

noncomputable def path_of_candidate (diagram : layered_diagram) (candidate : ℕ → ℕ) : ℕ → ℕ :=
  fun layer => if layer < diagram.layer_count then candidate (arc_of layer) else 0

noncomputable def candidate_of_path (diagram : layered_diagram) (path : ℕ → ℕ) : ℕ → ℕ := fun x =>
  if x % 3 = 0 then (if x / 3 < diagram.layer_count then diagram.label (x / 3) (path (x / 3)) else 0)
  else if x % 3 = 1 then (if x / 3 < diagram.layer_count then path (x / 3) else 0)
  else if x / 3 < diagram.layer_count then diagram.source (x / 3) (path (x / 3))
  else if x / 3 = diagram.layer_count then
    diagram.target (diagram.layer_count - 1) (path (diagram.layer_count - 1)) else 0

theorem candidate_of_path_original (diagram : layered_diagram) (path : ℕ → ℕ) (layer : ℕ)
    (layer_lt : layer < diagram.layer_count) :
    candidate_of_path diagram path (original_of layer) = diagram.label layer (path layer) := by
  have first : original_of layer % 3 = 0 := by unfold original_of; omega
  have quotient : original_of layer / 3 = layer := by unfold original_of; omega
  simp [candidate_of_path, first, quotient, layer_lt]

theorem candidate_of_path_arc (diagram : layered_diagram) (path : ℕ → ℕ) (layer : ℕ)
    (layer_lt : layer < diagram.layer_count) :
    candidate_of_path diagram path (arc_of layer) = path layer := by
  have first : arc_of layer % 3 = 1 := by unfold arc_of; omega
  have quotient : arc_of layer / 3 = layer := by unfold arc_of; omega
  simp [candidate_of_path, first, quotient, layer_lt]

theorem candidate_of_path_source (diagram : layered_diagram) (path : ℕ → ℕ) (layer : ℕ)
    (layer_lt : layer < diagram.layer_count) :
    candidate_of_path diagram path (node_of layer) = diagram.source layer (path layer) := by
  have first : node_of layer % 3 = 2 := by unfold node_of; omega
  have quotient : node_of layer / 3 = layer := by unfold node_of; omega
  simp [candidate_of_path, first, quotient, layer_lt]

theorem candidate_of_path_target (diagram : layered_diagram) (path : ℕ → ℕ)
    (is_path_path : is_path diagram path) (layer : ℕ) (layer_lt : layer < diagram.layer_count) :
    candidate_of_path diagram path (node_of (layer + 1)) = diagram.target layer (path layer) := by
  by_cases inner : layer + 1 < diagram.layer_count
  · rw [candidate_of_path_source diagram path (layer + 1) inner]
    exact (is_path_path.2.1 layer inner).symm
  · have last : layer + 1 = diagram.layer_count := by omega
    have first : node_of (layer + 1) % 3 = 2 := by unfold node_of; omega
    have quotient : node_of (layer + 1) / 3 = layer + 1 := by unfold node_of; omega
    have previous : diagram.layer_count - 1 = layer := by omega
    unfold candidate_of_path
    rw [ite_eq_right (by omega), ite_eq_right (by omega), quotient, ite_eq_right inner, ite_eq_left last, previous]

theorem candidate_of_path_outside (diagram : layered_diagram) (path : ℕ → ℕ) (x : ℕ)
    (x_out : x ∉ (dtbe diagram).vertices) : candidate_of_path diagram path x = 0 := by
  rw [mem_vertices] at x_out
  simp only [not_or, not_exists, not_and, original_of, arc_of, node_of] at x_out
  obtain ⟨no_original, no_arc, no_node⟩ := x_out
  have rest_cases : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases rest_cases with zero | one | two
  · have not_lt : ¬ x / 3 < diagram.layer_count := fun lt => no_original (x / 3) lt (by omega)
    simp [candidate_of_path, zero, not_lt]
  · have not_lt : ¬ x / 3 < diagram.layer_count := fun lt => no_arc (x / 3) lt (by omega)
    simp [candidate_of_path, one, not_lt]
  · have not_le : ¬ x / 3 ≤ diagram.layer_count := fun le => no_node (x / 3) le (by omega)
    have not_lt : ¬ x / 3 < diagram.layer_count := fun lt => not_le lt.le
    have not_eq : ¬ x / 3 = diagram.layer_count := fun eq => not_le eq.le
    simp [candidate_of_path, two, not_lt, not_eq]

theorem candidate_of_path_solution (diagram : layered_diagram) (path : ℕ → ℕ)
    (is_path_path : is_path diagram path) :
    is_solution (dtbe diagram) (candidate_of_path diagram path) := by
  rw [dtbe_solution_iff]
  refine ⟨fun layer layer_lt => ?_, fun layer layer_lt => ?_, fun layer layer_le => ?_,
    candidate_of_path_outside diagram path⟩
  · rw [candidate_of_path_arc diagram path layer layer_lt,
      candidate_of_path_original diagram path layer layer_lt,
      candidate_of_path_source diagram path layer layer_lt,
      candidate_of_path_target diagram path is_path_path layer layer_lt]
    exact ⟨(is_path_path.1 layer layer_lt).1, rfl, rfl, rfl⟩
  · rw [candidate_of_path_original diagram path layer layer_lt]
    exact (is_path_path.1 layer layer_lt).2.1
  · by_cases inner : layer < diagram.layer_count
    · rw [candidate_of_path_source diagram path layer inner]
      exact (is_path_path.1 layer inner).2.2.1
    · obtain ⟨previous, rfl⟩ : ∃ previous, layer = previous + 1 :=
        ⟨layer - 1, by have := diagram.layer_pos; omega⟩
      rw [candidate_of_path_target diagram path is_path_path previous (by omega)]
      exact (is_path_path.1 previous (by omega)).2.2.2

theorem path_of_candidate_is_path (diagram : layered_diagram) (candidate : ℕ → ℕ)
    (solution : is_solution (dtbe diagram) candidate) :
    is_path diagram (path_of_candidate diagram candidate) := by
  obtain ⟨follows, at_originals, at_nodes, _⟩ := (dtbe_solution_iff diagram candidate).mp solution
  refine ⟨fun layer layer_lt => ?_, fun layer inner => ?_, fun layer beyond => ?_⟩
  · have at_layer := follows layer layer_lt
    simp only [path_of_candidate, layer_lt, ite_true]
    refine ⟨at_layer.1, ?_, ?_, ?_⟩
    · rw [← at_layer.2.1]
      exact at_originals layer layer_lt
    · rw [← at_layer.2.2.1]
      exact at_nodes layer layer_lt.le
    · rw [← at_layer.2.2.2]
      exact at_nodes (layer + 1) layer_lt
  · have before : layer < diagram.layer_count := by omega
    simp only [path_of_candidate, before, inner, ite_true]
    rw [← (follows layer before).2.2.2, ← (follows (layer + 1) inner).2.2.1]
  · have not_lt : ¬ layer < diagram.layer_count := by omega
    simp [path_of_candidate, not_lt]

theorem candidate_of_path_of_candidate (diagram : layered_diagram) (candidate : ℕ → ℕ)
    (solution : is_solution (dtbe diagram) candidate) :
    candidate_of_path diagram (path_of_candidate diagram candidate) = candidate := by
  have is_path_path := path_of_candidate_is_path diagram candidate solution
  obtain ⟨follows, _, _, outside⟩ := (dtbe_solution_iff diagram candidate).mp solution
  have arc_value : ∀ layer, layer < diagram.layer_count →
      path_of_candidate diagram candidate layer = candidate (arc_of layer) := by
    intro layer layer_lt
    simp [path_of_candidate, layer_lt]
  funext x
  by_cases x_vertex : x ∈ (dtbe diagram).vertices
  · rcases (mem_vertices diagram x).mp x_vertex with
      ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_le, rfl⟩
    · rw [candidate_of_path_original diagram _ layer layer_lt, arc_value layer layer_lt]
      exact (follows layer layer_lt).2.1.symm
    · rw [candidate_of_path_arc diagram _ layer layer_lt, arc_value layer layer_lt]
    · by_cases inner : layer < diagram.layer_count
      · rw [candidate_of_path_source diagram _ layer inner, arc_value layer inner]
        exact (follows layer inner).2.2.1.symm
      · obtain ⟨previous, rfl⟩ : ∃ previous, layer = previous + 1 :=
          ⟨layer - 1, by have := diagram.layer_pos; omega⟩
        rw [candidate_of_path_target diagram _ is_path_path previous (by omega),
          arc_value previous (by omega)]
        exact (follows previous (by omega)).2.2.2.symm
  · rw [candidate_of_path_outside diagram _ x x_vertex, outside x x_vertex]

theorem path_of_candidate_of_path (diagram : layered_diagram) (path : ℕ → ℕ)
    (is_path_path : is_path diagram path) :
    path_of_candidate diagram (candidate_of_path diagram path) = path := by
  funext layer
  by_cases layer_lt : layer < diagram.layer_count
  · simp only [path_of_candidate, layer_lt, ite_true]
    exact candidate_of_path_arc diagram path layer layer_lt
  · simp only [path_of_candidate, layer_lt, ite_false]
    exact (is_path_path.2.2 layer (by omega)).symm

theorem extensions_eq_image_of_paths (diagram : layered_diagram) (tuple : ℕ → ℕ) :
    extensions (dtbe diagram) tuple = candidate_of_path diagram '' paths_spelling diagram tuple := by
  ext candidate
  constructor
  · rintro ⟨solution, agrees⟩
    refine ⟨path_of_candidate diagram candidate,
      ⟨path_of_candidate_is_path diagram candidate solution, fun layer layer_lt => ?_⟩,
      candidate_of_path_of_candidate diagram candidate solution⟩
    have at_layer := ((dtbe_solution_iff diagram candidate).mp solution).1 layer layer_lt
    simp only [path_of_candidate, layer_lt, ite_true]
    rw [← at_layer.2.1]
    exact agrees _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr layer_lt))
  · rintro ⟨path, ⟨is_path_path, spells⟩, rfl⟩
    refine ⟨candidate_of_path_solution diagram path is_path_path, fun x x_original => ?_⟩
    obtain ⟨layer, layer_mem, rfl⟩ := Finset.mem_image.mp x_original
    have layer_lt := Finset.mem_range.mp layer_mem
    rw [candidate_of_path_original diagram path layer layer_lt]
    exact spells layer layer_lt

theorem dtbe_extension_count_eq_path_count (diagram : layered_diagram) (tuple : ℕ → ℕ) :
    extension_count (dtbe diagram) tuple = (paths_spelling diagram tuple).ncard := by
  unfold extension_count
  rw [extensions_eq_image_of_paths]
  refine Set.InjOn.ncard_image fun first first_mem second second_mem same => ?_
  rw [← path_of_candidate_of_path diagram first first_mem.1,
    ← path_of_candidate_of_path diagram second second_mem.1, same]

def is_deterministic (diagram : layered_diagram) : Prop :=
  ∀ layer < diagram.layer_count, ∀ first ∈ diagram.arcs layer, ∀ second ∈ diagram.arcs layer,
    diagram.source layer first = diagram.source layer second →
      diagram.label layer first = diagram.label layer second → first = second

theorem deterministic_path_unique (diagram : layered_diagram) (deterministic : is_deterministic diagram)
    (one_root : (diagram.nodes 0).card = 1) (tuple first second : ℕ → ℕ)
    (first_spells : first ∈ paths_spelling diagram tuple)
    (second_spells : second ∈ paths_spelling diagram tuple) : first = second := by
  obtain ⟨⟨first_arcs, first_joined, first_beyond⟩, first_labels⟩ := first_spells
  obtain ⟨⟨second_arcs, second_joined, second_beyond⟩, second_labels⟩ := second_spells
  have same_label : ∀ layer < diagram.layer_count,
      diagram.label layer (first layer) = diagram.label layer (second layer) := fun layer layer_lt =>
    (first_labels layer layer_lt).trans (second_labels layer layer_lt).symm
  have step : ∀ layer, layer < diagram.layer_count → first layer = second layer := by
    intro layer
    induction layer with
    | zero =>
      intro layer_lt
      obtain ⟨root, root_only⟩ := Finset.card_eq_one.mp one_root
      have first_root := (first_arcs 0 layer_lt).2.2.1
      have second_root := (second_arcs 0 layer_lt).2.2.1
      rw [root_only, Finset.mem_singleton] at first_root second_root
      exact deterministic 0 layer_lt _ (first_arcs 0 layer_lt).1 _ (second_arcs 0 layer_lt).1
        (first_root.trans second_root.symm) (same_label 0 layer_lt)
    | succ layer hypothesis =>
      intro layer_lt
      have before := hypothesis (by omega)
      refine deterministic (layer + 1) layer_lt _ (first_arcs _ layer_lt).1 _
        (second_arcs _ layer_lt).1 ?_ (same_label _ layer_lt)
      rw [← first_joined layer layer_lt, ← second_joined layer layer_lt, before]
  funext layer
  by_cases layer_lt : layer < diagram.layer_count
  · exact step layer layer_lt
  · rw [first_beyond layer (by omega), second_beyond layer (by omega)]

theorem deterministic_dtbe_unique_extension (diagram : layered_diagram)
    (deterministic : is_deterministic diagram) (one_root : (diagram.nodes 0).card = 1) :
    has_unique_extension (dtbe diagram) := by
  intro tuple relation
  have positive := (extension_count_pos_iff (dtbe diagram) tuple).mpr relation
  rw [dtbe_extension_count_eq_path_count] at positive ⊢
  have finite : (paths_spelling diagram tuple).Finite := Set.finite_of_ncard_pos positive
  have at_most_one : (paths_spelling diagram tuple).ncard ≤ 1 := by
    rw [Set.ncard_le_one finite]
    exact fun first first_mem second second_mem =>
      deterministic_path_unique diagram deterministic one_root tuple first second first_mem second_mem
  omega

theorem algorithm_one_on_deterministic_dtbe (diagram : layered_diagram)
    (deterministic : is_deterministic diagram) (one_root : (diagram.nodes 0).card = 1) (reduced : bct)
    (run : is_algorithm_one_run (dtbe diagram) reduced) : has_unique_extension reduced :=
  algorithm_one_keeps_unique_extension (dtbe diagram) reduced run
    (deterministic_dtbe_unique_extension diagram deterministic one_root)

def is_trimmed (diagram : layered_diagram) : Prop :=
  (∀ layer < diagram.layer_count, ∀ e ∈ diagram.arcs layer,
    ∃ path, is_path diagram path ∧ path layer = e) ∧
  (∀ layer < diagram.layer_count, ∀ n ∈ diagram.nodes layer,
    ∃ path, is_path diagram path ∧ diagram.source layer (path layer) = n) ∧
  ∀ n ∈ diagram.nodes diagram.layer_count, ∃ path, is_path diagram path ∧
    diagram.target (diagram.layer_count - 1) (path (diagram.layer_count - 1)) = n

theorem trimmed_hidden_values_on_solutions (diagram : layered_diagram) (trimmed : is_trimmed diagram)
    (h : ℕ) (h_vertex : h ∈ (dtbe diagram).vertices) (h_hidden : h ∉ (dtbe diagram).originals) (a : ℕ)
    (a_mem : a ∈ (dtbe diagram).domain h) :
    ∃ candidate, is_solution (dtbe diagram) candidate ∧ candidate h = a := by
  rcases (mem_vertices diagram h).mp h_vertex with
    ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_lt, rfl⟩ | ⟨layer, layer_le, rfl⟩
  · exact absurd (Finset.mem_image_of_mem _ (Finset.mem_range.mpr layer_lt)) h_hidden
  · rw [arc_domain] at a_mem
    obtain ⟨path, is_path_path, at_layer⟩ := trimmed.1 layer layer_lt a a_mem
    exact ⟨_, candidate_of_path_solution diagram path is_path_path,
      (candidate_of_path_arc diagram path layer layer_lt).trans at_layer⟩
  · rw [node_domain] at a_mem
    by_cases inner : layer < diagram.layer_count
    · obtain ⟨path, is_path_path, at_layer⟩ := trimmed.2.1 layer inner a a_mem
      exact ⟨_, candidate_of_path_solution diagram path is_path_path,
        (candidate_of_path_source diagram path layer inner).trans at_layer⟩
    · have last : layer = diagram.layer_count := by omega
      subst last
      obtain ⟨path, is_path_path, at_end⟩ := trimmed.2.2 a a_mem
      refine ⟨_, candidate_of_path_solution diagram path is_path_path, ?_⟩
      have positive := diagram.layer_pos
      have restore : diagram.layer_count - 1 + 1 = diagram.layer_count := by omega
      have at_target := candidate_of_path_target diagram path is_path_path (diagram.layer_count - 1)
        (by omega)
      rw [restore] at at_target
      exact at_target.trans at_end

end rules
end parsimony
