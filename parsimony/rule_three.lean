import parsimony.minimal_support_counting

namespace parsimony

variable {vertex_count : ℕ}

abbrev pair_rest (csp : binary_csp vertex_count) (h k : Fin vertex_count) :=
  ∀ x : {x : Fin vertex_count // x ≠ h ∧ x ≠ k}, Fin (csp.domain_size x.val)

def assemble_pair (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (rest : pair_rest csp h k) (first : Fin (csp.domain_size h))
    (second : Fin (csp.domain_size k)) : assignment csp :=
  Function.update
    (Function.update
      (fun x => if other : x ≠ h ∧ x ≠ k then rest ⟨x, other⟩ else ⟨0, csp.domain_nonempty x⟩)
      h first)
    k second

def is_merged_solution (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (rest : pair_rest csp h k) (first : Fin (csp.domain_size h))
    (second : Fin (csp.domain_size k)) : Prop :=
  (∀ x y : {x : Fin vertex_count // x ≠ h ∧ x ≠ k}, csp.adjacent x.val y.val = true →
    csp.allowed x.val y.val (rest x) (rest y) = true) ∧
  csp.allowed h k first second = true ∧
  (∀ z : {x : Fin vertex_count // x ≠ h ∧ x ≠ k}, csp.adjacent h z.val = true →
    csp.allowed h z.val first (rest z) = true) ∧
  ∀ z : {x : Fin vertex_count // x ≠ h ∧ x ≠ k}, csp.adjacent k z.val = true →
    csp.allowed k z.val second (rest z) = true

def pair_rest_encodes (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (h k : Fin vertex_count) (rest : pair_rest csp h k) (tuple : original_tuple csp originals) :
    Prop :=
  ∀ x : {x : Fin vertex_count // x ≠ h ∧ x ≠ k}, ∀ on_x : originals x.val = true,
    rest x = tuple ⟨x.val, on_x⟩

open Classical in
noncomputable def merged_extension_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (h k : Fin vertex_count)
    (tuple : original_tuple csp originals) : ℕ :=
  Fintype.card {triple : pair_rest csp h k × Fin (csp.domain_size h) × Fin (csp.domain_size k) //
    is_merged_solution csp h k triple.1 triple.2.1 triple.2.2 ∧
      pair_rest_encodes csp originals h k triple.1 tuple}

theorem assemble_pair_at_second (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (rest : pair_rest csp h k) (first : Fin (csp.domain_size h))
    (second : Fin (csp.domain_size k)) :
    assemble_pair csp h k rest first second k = second := by
  unfold assemble_pair
  rw [Function.update_self]

theorem assemble_pair_at_first (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (h_ne_k : h ≠ k) (rest : pair_rest csp h k) (first : Fin (csp.domain_size h))
    (second : Fin (csp.domain_size k)) :
    assemble_pair csp h k rest first second h = first := by
  unfold assemble_pair
  rw [Function.update_of_ne h_ne_k, Function.update_self]

theorem assemble_pair_at_other (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (rest : pair_rest csp h k) (first : Fin (csp.domain_size h))
    (second : Fin (csp.domain_size k)) (x : Fin vertex_count) (other : x ≠ h ∧ x ≠ k) :
    assemble_pair csp h k rest first second x = rest ⟨x, other⟩ := by
  unfold assemble_pair
  rw [Function.update_of_ne other.2, Function.update_of_ne other.1]
  exact dite_eq_left_of_eq_true (eq_true other)

theorem vertex_cases (h k x : Fin vertex_count) : x = h ∨ x = k ∨ (x ≠ h ∧ x ≠ k) := by
  by_cases x_is_h : x = h
  · exact Or.inl x_is_h
  · by_cases x_is_k : x = k
    · exact Or.inr (Or.inl x_is_k)
    · exact Or.inr (Or.inr ⟨x_is_h, x_is_k⟩)

theorem merged_solution_iff (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (adjacent_h_k : csp.adjacent h k = true) (rest : pair_rest csp h k)
    (first : Fin (csp.domain_size h)) (second : Fin (csp.domain_size k)) :
    is_merged_solution csp h k rest first second ↔
      is_solution csp (assemble_pair csp h k rest first second) := by
  have h_ne_k : h ≠ k := adjacent_ne csp h k adjacent_h_k
  have at_h := assemble_pair_at_first csp h k h_ne_k rest first second
  have at_k := assemble_pair_at_second csp h k rest first second
  have at_other := assemble_pair_at_other csp h k rest first second
  constructor
  · rintro ⟨rest_ok, pair_ok, h_ok, k_ok⟩ x y adjacent_x_y
    rcases vertex_cases h k x with x_is_h | x_is_k | x_other <;>
      rcases vertex_cases h k y with y_is_h | y_is_k | y_other
    · rw [x_is_h, y_is_h, csp.adjacent_irrefl] at adjacent_x_y
      exact absurd adjacent_x_y (by decide)
    · rw [x_is_h, y_is_k, at_h, at_k]
      exact pair_ok
    · have adjacent_h_y : csp.adjacent h y = true := by
        rw [← x_is_h]
        exact adjacent_x_y
      rw [x_is_h, at_h, at_other y y_other]
      exact h_ok ⟨y, y_other⟩ adjacent_h_y
    · rw [x_is_k, y_is_h, at_k, at_h, csp.allowed_symm]
      exact pair_ok
    · rw [x_is_k, y_is_k, csp.adjacent_irrefl] at adjacent_x_y
      exact absurd adjacent_x_y (by decide)
    · have adjacent_k_y : csp.adjacent k y = true := by
        rw [← x_is_k]
        exact adjacent_x_y
      rw [x_is_k, at_k, at_other y y_other]
      exact k_ok ⟨y, y_other⟩ adjacent_k_y
    · have adjacent_h_x : csp.adjacent h x = true := by
        rw [csp.adjacent_symm, ← y_is_h]
        exact adjacent_x_y
      rw [y_is_h, at_h, at_other x x_other, csp.allowed_symm]
      exact h_ok ⟨x, x_other⟩ adjacent_h_x
    · have adjacent_k_x : csp.adjacent k x = true := by
        rw [csp.adjacent_symm, ← y_is_k]
        exact adjacent_x_y
      rw [y_is_k, at_k, at_other x x_other, csp.allowed_symm]
      exact k_ok ⟨x, x_other⟩ adjacent_k_x
    · rw [at_other x x_other, at_other y y_other]
      exact rest_ok ⟨x, x_other⟩ ⟨y, y_other⟩ adjacent_x_y
  · intro solution
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y adjacent_x_y
      have edge := solution x.val y.val adjacent_x_y
      rw [at_other x.val x.property, at_other y.val y.property] at edge
      exact edge
    · have edge := solution h k adjacent_h_k
      rw [at_h, at_k] at edge
      exact edge
    · intro z adjacent_h_z
      have edge := solution h z.val adjacent_h_z
      rw [at_h, at_other z.val z.property] at edge
      exact edge
    · intro z adjacent_k_z
      have edge := solution k z.val adjacent_k_z
      rw [at_k, at_other z.val z.property] at edge
      exact edge

theorem assemble_pair_of_candidate (csp : binary_csp vertex_count) (h k : Fin vertex_count)
    (h_ne_k : h ≠ k) (candidate : assignment csp) :
    assemble_pair csp h k (fun x => candidate x.val) (candidate h) (candidate k) = candidate := by
  funext x
  rcases vertex_cases h k x with x_is_h | x_is_k | x_other
  · subst x_is_h
    exact assemble_pair_at_first csp x k h_ne_k _ _ _
  · subst x_is_k
    exact assemble_pair_at_second csp h x _ _ _
  · exact assemble_pair_at_other csp h k _ _ _ x x_other

theorem rule_three_keeps_extension_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (h k : Fin vertex_count)
    (h_hidden : originals h = false) (k_hidden : originals k = false)
    (adjacent_h_k : csp.adjacent h k = true) (tuple : original_tuple csp originals) :
    merged_extension_count csp originals h k tuple = extension_count csp originals tuple := by
  classical
  have h_ne_k : h ≠ k := adjacent_ne csp h k adjacent_h_k
  have original_other : ∀ x, originals x = true → x ≠ h ∧ x ≠ k := by
    intro x on_x
    constructor
    · intro x_is_h
      rw [x_is_h, h_hidden] at on_x
      exact absurd on_x (by decide)
    · intro x_is_k
      rw [x_is_k, k_hidden] at on_x
      exact absurd on_x (by decide)
  have forget_merged : ∀ candidate : assignment csp, is_solution csp candidate →
      is_merged_solution csp h k (fun x => candidate x.val) (candidate h) (candidate k) := by
    intro candidate solution
    apply (merged_solution_iff csp h k adjacent_h_k _ _ _).mpr
    rw [assemble_pair_of_candidate csp h k h_ne_k candidate]
    exact solution
  have forget_encodes : ∀ candidate : assignment csp,
      restrict_to_originals csp originals candidate = tuple →
        pair_rest_encodes csp originals h k (fun x => candidate x.val) tuple := by
    intro candidate restricted x on_x
    exact congrFun restricted ⟨x.val, on_x⟩
  unfold merged_extension_count extension_count
  symm
  refine Fintype.card_of_bijective
    (f := fun candidate => ⟨((fun x => candidate.val x.val), candidate.val h, candidate.val k),
      forget_merged candidate.val candidate.property.1,
      forget_encodes candidate.val candidate.property.2⟩) ⟨?_, ?_⟩
  · intro first second same_image
    have same := congrArg Subtype.val same_image
    simp only [Prod.mk.injEq] at same
    obtain ⟨same_rest, same_h, same_k⟩ := same
    apply Subtype.ext
    funext x
    rcases vertex_cases h k x with x_is_h | x_is_k | x_other
    · subst x_is_h
      exact same_h
    · subst x_is_k
      exact same_k
    · exact congrFun same_rest ⟨x, x_other⟩
  · rintro ⟨⟨rest, first, second⟩, merged, encodes⟩
    have solution := (merged_solution_iff csp h k adjacent_h_k rest first second).mp merged
    have restricted : restrict_to_originals csp originals
        (assemble_pair csp h k rest first second) = tuple := by
      funext x
      have other := original_other x.val x.property
      show assemble_pair csp h k rest first second x.val = tuple x
      rw [assemble_pair_at_other csp h k rest first second x.val other]
      exact encodes ⟨x.val, other⟩ x.property
    refine ⟨⟨assemble_pair csp h k rest first second, solution, restricted⟩, ?_⟩
    apply Subtype.ext
    show ((fun x : {x : Fin vertex_count // x ≠ h ∧ x ≠ k} =>
        assemble_pair csp h k rest first second x.val),
        assemble_pair csp h k rest first second h, assemble_pair csp h k rest first second k) =
      (rest, first, second)
    rw [assemble_pair_at_first csp h k h_ne_k, assemble_pair_at_second]
    congr 1
    funext x
    exact assemble_pair_at_other csp h k rest first second x.val x.property

end parsimony
