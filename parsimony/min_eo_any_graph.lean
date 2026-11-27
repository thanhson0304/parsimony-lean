import parsimony.bijection
import parsimony.counterexamples

namespace parsimony

variable {vertex_count : ℕ}

def kept_support_clauses (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool) :
    cnf_formula (boolean_variable csp all_vertices) :=
  clauses_on_chosen_pairs (fun x y => csp.adjacent x y && kept x y)
    (support_clauses_of_pair csp all_vertices)

def min_eo_any_graph_encoding (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool) :
    cnf_formula (boolean_variable csp all_vertices) :=
  exactly_one_part csp all_vertices ++ kept_support_clauses csp kept

def keeps_one_direction (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool) : Prop :=
  ∀ x y, csp.adjacent x y = true → kept x y = true ∨ kept y x = true

theorem is_model_min_eo_any_graph_iff (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (min_eo_any_graph_encoding csp kept) ↔
      (∀ x (on_x : all_vertices x = true),
        ∃ chosen, block_is_fixed csp all_vertices valuation x on_x chosen) ∧
      ∀ x y, csp.adjacent x y = true → kept x y = true →
        edge_is_supported csp all_vertices valuation x y := by
  rw [min_eo_any_graph_encoding, is_model_append, is_model_exactly_one_part_iff,
    kept_support_clauses, is_model_clauses_on_chosen_pairs_iff]
  simp only [Bool.and_eq_true, is_model_support_clauses_of_pair_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    exact ⟨blocks, fun x y adjacent_x_y kept_x_y => edges x y ⟨adjacent_x_y, kept_x_y⟩⟩
  · rintro ⟨blocks, edges⟩
    exact ⟨blocks, fun x y chosen => edges x y chosen.1 chosen.2⟩

theorem min_eo_any_graph_model_iff (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool)
    (one_direction : keeps_one_direction csp kept)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (min_eo_any_graph_encoding csp kept) ↔
      ∃ candidate, is_solution csp candidate ∧
        valuation = valuation_of_assignment csp all_vertices candidate := by
  rw [is_model_min_eo_any_graph_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    obtain ⟨candidate, rfl⟩ := valuation_is_assignment_of_blocks csp valuation blocks
    refine ⟨candidate, ?_, rfl⟩
    have directed : ∀ x y, csp.adjacent x y = true → kept x y = true →
        csp.allowed x y (candidate x) (candidate y) = true := by
      intro x y adjacent_x_y kept_x_y
      obtain ⟨b, b_allowed, b_selected⟩ := edges x y adjacent_x_y kept_x_y (candidate x)
        (by simp [valuation_of_assignment])
      have b_is_candidate : b = candidate y := by simpa [valuation_of_assignment] using b_selected
      rw [← b_is_candidate]
      exact b_allowed
    intro x y adjacent_x_y
    rcases one_direction x y adjacent_x_y with kept_x_y | kept_y_x
    · exact directed x y adjacent_x_y kept_x_y
    · rw [csp.allowed_symm x y]
      refine directed y x ?_ kept_y_x
      rw [csp.adjacent_symm]
      exact adjacent_x_y
  · rintro ⟨candidate, solution, rfl⟩
    exact ⟨fun x on_x => ⟨candidate x, valuation_of_assignment_block csp all_vertices candidate x on_x⟩,
      fun x y adjacent_x_y _ =>
        valuation_of_solution_edge csp all_vertices candidate solution x y adjacent_x_y⟩

theorem min_eo_any_graph_model_count (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool)
    (one_direction : keeps_one_direction csp kept) :
    model_count (min_eo_any_graph_encoding csp kept) =
      Fintype.card {candidate : assignment csp // is_solution csp candidate} :=
  model_count_eq_solution_count csp _ (min_eo_any_graph_model_iff csp kept one_direction)

theorem min_eo_any_graph_is_projection_exact (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool)
    (one_direction : keeps_one_direction csp kept) (originals : Fin vertex_count → Bool) :
    is_projection_exact csp originals all_vertices (min_eo_any_graph_encoding csp kept) :=
  projection_exact_of_model_iff csp _ (min_eo_any_graph_model_iff csp kept one_direction) originals

theorem min_eo_any_graph_models_over_tuple (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool)
    (one_direction : keeps_one_direction csp kept) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) :
    models_over_tuple csp originals all_vertices (min_eo_any_graph_encoding csp kept) tuple =
      extension_count csp originals tuple :=
  models_over_tuple_eq_extension_count csp _ (min_eo_any_graph_model_iff csp kept one_direction)
    originals tuple

theorem min_eo_any_graph_parsimonious_iff (csp : binary_csp vertex_count)
    (kept : Fin vertex_count → Fin vertex_count → Bool)
    (one_direction : keeps_one_direction csp kept) (originals : Fin vertex_count → Bool) :
    is_parsimonious csp originals (min_eo_any_graph_encoding csp kept) ↔
      has_unique_extension csp originals :=
  parsimonious_iff_unique_extension_of_model_iff csp _
    (min_eo_any_graph_model_iff csp kept one_direction) originals

theorem min_eo_encoding_eq_any_graph (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) :
    min_eo_encoding csp order = min_eo_any_graph_encoding csp (earlier_in order) := rfl

theorem keeps_one_direction_of_listing (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (listed : ∀ x, x ∈ order) :
    keeps_one_direction csp (earlier_in order) := by
  intro x y adjacent_x_y
  have x_ne_y : x ≠ y := by
    intro x_is_y
    subst x_is_y
    rw [csp.adjacent_irrefl] at adjacent_x_y
    exact absurd adjacent_x_y (by decide)
  have differ : order.idxOf x ≠ order.idxOf y := by
    intro same_position
    exact x_ne_y ((List.idxOf_inj (listed x)).mp same_position)
  rcases Nat.lt_or_gt_of_ne differ with x_earlier | y_earlier
  · exact Or.inl (by simpa [earlier_in] using x_earlier)
  · exact Or.inr (by simpa [earlier_in] using y_earlier)

theorem min_eo_listing_model_count (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (listed : ∀ x, x ∈ order) :
    model_count (min_eo_encoding csp order) =
      Fintype.card {candidate : assignment csp // is_solution csp candidate} := by
  rw [min_eo_encoding_eq_any_graph]
  exact min_eo_any_graph_model_count csp _ (keeps_one_direction_of_listing csp order listed)

theorem min_eo_listing_is_projection_exact (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (listed : ∀ x, x ∈ order)
    (originals : Fin vertex_count → Bool) :
    is_projection_exact csp originals all_vertices (min_eo_encoding csp order) := by
  rw [min_eo_encoding_eq_any_graph]
  exact min_eo_any_graph_is_projection_exact csp _ (keeps_one_direction_of_listing csp order listed)
    originals

theorem min_eo_listing_models_over_tuple (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (listed : ∀ x, x ∈ order)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals) :
    models_over_tuple csp originals all_vertices (min_eo_encoding csp order) tuple =
      extension_count csp originals tuple := by
  rw [min_eo_encoding_eq_any_graph]
  exact min_eo_any_graph_models_over_tuple csp _ (keeps_one_direction_of_listing csp order listed)
    originals tuple

theorem min_eo_listing_parsimonious_iff (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (listed : ∀ x, x ∈ order)
    (originals : Fin vertex_count → Bool) :
    is_parsimonious csp originals (min_eo_encoding csp order) ↔
      has_unique_extension csp originals := by
  rw [min_eo_encoding_eq_any_graph]
  exact min_eo_any_graph_parsimonious_iff csp _ (keeps_one_direction_of_listing csp order listed)
    originals

def any_graph_triangle_csp : binary_csp 3 :=
  counterexamples.csp_of_edges 3 [2, 2, 2]
    [(0, 1, [(0, 0), (1, 1)]), (1, 2, [(0, 0), (1, 1)]), (0, 2, [(0, 0), (1, 1)])]
    (by decide) (by decide)

theorem any_graph_triangle_has_three_edges :
    (Finset.univ.filter fun pair : Fin 3 × Fin 3 =>
      any_graph_triangle_csp.adjacent pair.1 pair.2 = true).card = 6 := by
  decide +kernel

theorem any_graph_triangle_order_listed : ∀ x : Fin 3, x ∈ [0, 1, 2] := by
  decide

theorem any_graph_triangle_solution_count :
    Fintype.card {candidate : assignment any_graph_triangle_csp //
      is_solution any_graph_triangle_csp candidate} = 2 := by
  decide +kernel

theorem any_graph_triangle_model_count_by_theorem :
    model_count (min_eo_encoding any_graph_triangle_csp [0, 1, 2]) = 2 := by
  rw [min_eo_listing_model_count any_graph_triangle_csp [0, 1, 2] any_graph_triangle_order_listed]
  exact any_graph_triangle_solution_count

theorem any_graph_triangle_model_count_by_enumeration :
    model_count (min_eo_encoding any_graph_triangle_csp [0, 1, 2]) = 2 := by
  decide +kernel

theorem any_graph_triangle_order_is_not_tree_order :
    ¬ is_tree_order any_graph_triangle_csp [0, 1, 2] := by
  decide +kernel

def any_graph_left_out_csp : binary_csp 2 :=
  counterexamples.csp_of_edges 2 [2, 2] [(0, 1, [(0, 0)])] (by decide) (by decide)

def keeps_no_direction : Fin 2 → Fin 2 → Bool := fun _ _ => false

theorem any_graph_left_out_keeps_no_direction :
    ¬ keeps_one_direction any_graph_left_out_csp keeps_no_direction := by
  intro one_direction
  have adjacent_zero_one : any_graph_left_out_csp.adjacent 0 1 = true := by decide
  rcases one_direction 0 1 adjacent_zero_one with kept_zero_one | kept_one_zero
  · exact absurd kept_zero_one (by decide)
  · exact absurd kept_one_zero (by decide)

theorem any_graph_left_out_relation_count :
    relation_count any_graph_left_out_csp all_vertices = 1 := by
  decide +kernel

theorem any_graph_left_out_has_unique_extension :
    has_unique_extension any_graph_left_out_csp all_vertices := by
  decide +kernel

theorem any_graph_left_out_model_count :
    model_count (min_eo_any_graph_encoding any_graph_left_out_csp keeps_no_direction) = 4 := by
  decide +kernel

theorem any_graph_left_out_is_not_parsimonious :
    ¬ is_parsimonious any_graph_left_out_csp all_vertices
      (min_eo_any_graph_encoding any_graph_left_out_csp keeps_no_direction) := by
  rw [is_parsimonious, any_graph_left_out_model_count, any_graph_left_out_relation_count]
  decide

end parsimony
