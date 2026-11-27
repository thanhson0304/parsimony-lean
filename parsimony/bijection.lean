import parsimony.semantics

namespace parsimony

variable {vertex_count : ℕ}

theorem extension_count_eq_one_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals) :
    extension_count csp originals tuple = 1 ↔
      ∃! candidate, is_solution csp candidate ∧
        restrict_to_originals csp originals candidate = tuple := by
  unfold extension_count
  rw [Fintype.card_eq_one_iff]
  constructor
  · rintro ⟨⟨candidate, property⟩, unique⟩
    exact ⟨candidate, property,
      fun other other_property => congrArg Subtype.val (unique ⟨other, other_property⟩)⟩
  · rintro ⟨candidate, property, unique⟩
    exact ⟨⟨candidate, property⟩, fun other => Subtype.ext (unique other.val other.property)⟩

theorem valuation_is_assignment_of_blocks (csp : binary_csp vertex_count)
    (valuation : boolean_variable csp all_vertices → Bool)
    (blocks : ∀ x (on_x : all_vertices x = true),
      ∃ chosen, block_is_fixed csp all_vertices valuation x on_x chosen) :
    ∃ candidate : assignment csp,
      valuation = valuation_of_assignment csp all_vertices candidate := by
  choose candidate candidate_fixed using fun x => blocks x rfl
  refine ⟨candidate, ?_⟩
  funext variable_name
  rcases variable_name with ⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩
  · exact (candidate_fixed x).1 a
  · exact (candidate_fixed x).2 i

theorem support_model_iff (csp : binary_csp vertex_count)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (support_encoding csp) ↔
      ∃ candidate, is_solution csp candidate ∧
        valuation = valuation_of_assignment csp all_vertices candidate := by
  rw [is_model_support_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    obtain ⟨candidate, rfl⟩ := valuation_is_assignment_of_blocks csp valuation blocks
    refine ⟨candidate, ?_, rfl⟩
    intro x y adjacent_x_y
    obtain ⟨b, b_allowed, b_selected⟩ := edges x y adjacent_x_y (candidate x)
      (by simp [valuation_of_assignment])
    have b_is_candidate : b = candidate y := by simpa [valuation_of_assignment] using b_selected
    rw [← b_is_candidate]
    exact b_allowed
  · rintro ⟨candidate, solution, rfl⟩
    exact ⟨fun x on_x => ⟨candidate x, valuation_of_assignment_block csp all_vertices candidate x on_x⟩,
      fun x y adjacent_x_y =>
        valuation_of_solution_edge csp all_vertices candidate solution x y adjacent_x_y⟩

theorem direct_model_iff (csp : binary_csp vertex_count)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (direct_encoding csp) ↔
      ∃ candidate, is_solution csp candidate ∧
        valuation = valuation_of_assignment csp all_vertices candidate := by
  rw [is_model_direct_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    obtain ⟨candidate, rfl⟩ := valuation_is_assignment_of_blocks csp valuation blocks
    refine ⟨candidate, ?_, rfl⟩
    intro x y adjacent_x_y
    by_contra not_allowed
    have forbidden : csp.allowed x y (candidate x) (candidate y) = false := by
      simpa using not_allowed
    rcases edges x y adjacent_x_y (candidate x) (candidate y) forbidden with left | right
    · simp [valuation_of_assignment] at left
    · simp [valuation_of_assignment] at right
  · rintro ⟨candidate, solution, rfl⟩
    refine ⟨fun x on_x => ⟨candidate x, valuation_of_assignment_block csp all_vertices candidate x on_x⟩,
      ?_⟩
    intro x y adjacent_x_y a b forbidden
    by_cases a_is_candidate : a = candidate x
    · by_cases b_is_candidate : b = candidate y
      · have allowed_true := solution x y adjacent_x_y
        rw [← a_is_candidate, ← b_is_candidate, forbidden] at allowed_true
        exact absurd allowed_true (by decide)
      · right
        simp [valuation_of_assignment, b_is_candidate]
    · left
      simp [valuation_of_assignment, a_is_candidate]

theorem min_eo_model_iff (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order)
    (valuation : boolean_variable csp all_vertices → Bool) :
    is_model valuation (min_eo_encoding csp order) ↔
      ∃ candidate, is_solution csp candidate ∧
        valuation = valuation_of_assignment csp all_vertices candidate := by
  rw [is_model_min_eo_iff]
  constructor
  · rintro ⟨blocks, edges⟩
    obtain ⟨candidate, rfl⟩ := valuation_is_assignment_of_blocks csp valuation blocks
    refine ⟨candidate, ?_, rfl⟩
    have directed : ∀ x y, csp.adjacent x y = true → earlier_in order x y = true →
        csp.allowed x y (candidate x) (candidate y) = true := by
      intro x y adjacent_x_y x_earlier
      obtain ⟨b, b_allowed, b_selected⟩ := edges x y adjacent_x_y x_earlier (candidate x)
        (by simp [valuation_of_assignment])
      have b_is_candidate : b = candidate y := by simpa [valuation_of_assignment] using b_selected
      rw [← b_is_candidate]
      exact b_allowed
    intro x y adjacent_x_y
    have x_ne_y : x ≠ y := by
      intro x_is_y
      subst x_is_y
      rw [csp.adjacent_irrefl] at adjacent_x_y
      exact absurd adjacent_x_y (by decide)
    have differ := tree_order_positions_differ csp order tree_order x y x_ne_y
    rcases Nat.lt_or_gt_of_ne differ with x_earlier | y_earlier
    · exact directed x y adjacent_x_y (by simpa [earlier_in] using x_earlier)
    · rw [csp.allowed_symm x y]
      refine directed y x ?_ (by simpa [earlier_in] using y_earlier)
      rw [csp.adjacent_symm]
      exact adjacent_x_y
  · rintro ⟨candidate, solution, rfl⟩
    exact ⟨fun x on_x => ⟨candidate x, valuation_of_assignment_block csp all_vertices candidate x on_x⟩,
      fun x y adjacent_x_y _ =>
        valuation_of_solution_edge csp all_vertices candidate solution x y adjacent_x_y⟩

section encoding_correspondence

variable (csp : binary_csp vertex_count)
  (formula : cnf_formula (boolean_variable csp all_vertices))
  (model_iff : ∀ valuation, is_model valuation formula ↔
    ∃ candidate, is_solution csp candidate ∧
      valuation = valuation_of_assignment csp all_vertices candidate)

include model_iff

theorem model_count_eq_solution_count :
    model_count formula = Fintype.card {candidate : assignment csp // is_solution csp candidate} := by
  unfold model_count
  symm
  refine Fintype.card_of_bijective
    (f := fun candidate =>
      ⟨valuation_of_assignment csp all_vertices candidate.val,
        (model_iff _).mpr ⟨candidate.val, candidate.property, rfl⟩⟩) ⟨?_, ?_⟩
  · intro first second same_image
    exact Subtype.ext (valuation_of_assignment_injective csp all_vertices
      (congrArg Subtype.val same_image))
  · rintro ⟨valuation, model⟩
    obtain ⟨candidate, solution, rfl⟩ := (model_iff _).mp model
    exact ⟨⟨candidate, solution⟩, rfl⟩

theorem projection_exact_of_model_iff (originals : Fin vertex_count → Bool) :
    is_projection_exact csp originals all_vertices formula := by
  constructor
  · intro valuation model
    obtain ⟨candidate, solution, rfl⟩ := (model_iff _).mp model
    exact ⟨restrict_to_originals csp originals candidate, ⟨candidate, solution, rfl⟩,
      valuation_of_assignment_encodes csp originals all_vertices candidate⟩
  · rintro tuple ⟨candidate, solution, restricted⟩
    subst restricted
    exact ⟨valuation_of_assignment csp all_vertices candidate,
      (model_iff _).mpr ⟨candidate, solution, rfl⟩,
      valuation_of_assignment_encodes csp originals all_vertices candidate⟩

theorem models_over_tuple_eq_extension_count (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) :
    models_over_tuple csp originals all_vertices formula tuple =
      extension_count csp originals tuple := by
  unfold models_over_tuple extension_count
  symm
  refine Fintype.card_of_bijective
    (f := fun candidate =>
      ⟨valuation_of_assignment csp all_vertices candidate.val,
        (model_iff _).mpr ⟨candidate.val, candidate.property.1, rfl⟩, by
          have encodes := valuation_of_assignment_encodes csp originals all_vertices candidate.val
          rw [candidate.property.2] at encodes
          exact encodes⟩) ⟨?_, ?_⟩
  · intro first second same_image
    exact Subtype.ext (valuation_of_assignment_injective csp all_vertices
      (congrArg Subtype.val same_image))
  · rintro ⟨valuation, model, encodes⟩
    obtain ⟨candidate, solution, rfl⟩ := (model_iff _).mp model
    refine ⟨⟨candidate, solution, ?_⟩, rfl⟩
    exact encodes_tuple_unique csp originals all_vertices _ _ _
      (valuation_of_assignment_encodes csp originals all_vertices candidate) encodes

theorem parsimonious_iff_unique_extension_of_model_iff (originals : Fin vertex_count → Bool) :
    is_parsimonious csp originals formula ↔ has_unique_extension csp originals := by
  rw [is_parsimonious_iff_unique_models csp originals all_vertices formula
    (projection_exact_of_model_iff csp formula model_iff originals)]
  unfold has_unique_extension
  refine forall_congr' fun tuple => imp_congr_right fun _ => ?_
  rw [extension_count_eq_one_iff]
  constructor
  · rintro ⟨valuation, ⟨model, encodes⟩, unique⟩
    obtain ⟨candidate, solution, rfl⟩ := (model_iff _).mp model
    have candidate_restricted : restrict_to_originals csp originals candidate = tuple :=
      encodes_tuple_unique csp originals all_vertices _ _ _
        (valuation_of_assignment_encodes csp originals all_vertices candidate) encodes
    refine ⟨candidate, ⟨solution, candidate_restricted⟩, ?_⟩
    rintro other ⟨other_solution, other_restricted⟩
    have other_encodes : encodes_tuple csp originals all_vertices
        (valuation_of_assignment csp all_vertices other) tuple := by
      rw [← other_restricted]
      exact valuation_of_assignment_encodes csp originals all_vertices other
    exact valuation_of_assignment_injective csp all_vertices
      (unique _ ⟨(model_iff _).mpr ⟨other, other_solution, rfl⟩, other_encodes⟩)
  · rintro ⟨candidate, ⟨solution, restricted⟩, unique⟩
    have candidate_encodes : encodes_tuple csp originals all_vertices
        (valuation_of_assignment csp all_vertices candidate) tuple := by
      rw [← restricted]
      exact valuation_of_assignment_encodes csp originals all_vertices candidate
    refine ⟨valuation_of_assignment csp all_vertices candidate,
      ⟨(model_iff _).mpr ⟨candidate, solution, rfl⟩, candidate_encodes⟩, ?_⟩
    rintro other ⟨other_model, other_encodes⟩
    obtain ⟨other_candidate, other_solution, rfl⟩ := (model_iff _).mp other_model
    have other_restricted : restrict_to_originals csp originals other_candidate = tuple :=
      encodes_tuple_unique csp originals all_vertices _ _ _
        (valuation_of_assignment_encodes csp originals all_vertices other_candidate) other_encodes
    rw [unique other_candidate ⟨other_solution, other_restricted⟩]

end encoding_correspondence

theorem support_parsimonious_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_parsimonious csp originals (support_encoding csp) ↔ has_unique_extension csp originals :=
  parsimonious_iff_unique_extension_of_model_iff csp _ (support_model_iff csp) originals

theorem direct_parsimonious_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_parsimonious csp originals (direct_encoding csp) ↔ has_unique_extension csp originals :=
  parsimonious_iff_unique_extension_of_model_iff csp _ (direct_model_iff csp) originals

theorem min_eo_parsimonious_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) :
    is_parsimonious csp originals (min_eo_encoding csp order) ↔
      has_unique_extension csp originals :=
  parsimonious_iff_unique_extension_of_model_iff csp _
    (min_eo_model_iff csp order tree_order) originals

theorem support_model_count (csp : binary_csp vertex_count) :
    model_count (support_encoding csp) =
      Fintype.card {candidate : assignment csp // is_solution csp candidate} :=
  model_count_eq_solution_count csp _ (support_model_iff csp)

theorem direct_model_count (csp : binary_csp vertex_count) :
    model_count (direct_encoding csp) =
      Fintype.card {candidate : assignment csp // is_solution csp candidate} :=
  model_count_eq_solution_count csp _ (direct_model_iff csp)

theorem min_eo_model_count (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) :
    model_count (min_eo_encoding csp order) =
      Fintype.card {candidate : assignment csp // is_solution csp candidate} :=
  model_count_eq_solution_count csp _ (min_eo_model_iff csp order tree_order)

theorem support_is_projection_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_projection_exact csp originals all_vertices (support_encoding csp) :=
  projection_exact_of_model_iff csp _ (support_model_iff csp) originals

theorem direct_is_projection_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_projection_exact csp originals all_vertices (direct_encoding csp) :=
  projection_exact_of_model_iff csp _ (direct_model_iff csp) originals

theorem min_eo_is_projection_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) :
    is_projection_exact csp originals all_vertices (min_eo_encoding csp order) :=
  projection_exact_of_model_iff csp _ (min_eo_model_iff csp order tree_order) originals

theorem support_models_over_tuple (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals) :
    models_over_tuple csp originals all_vertices (support_encoding csp) tuple =
      extension_count csp originals tuple :=
  models_over_tuple_eq_extension_count csp _ (support_model_iff csp) originals tuple

theorem direct_models_over_tuple (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals) :
    models_over_tuple csp originals all_vertices (direct_encoding csp) tuple =
      extension_count csp originals tuple :=
  models_over_tuple_eq_extension_count csp _ (direct_model_iff csp) originals tuple

theorem min_eo_models_over_tuple (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (tuple : original_tuple csp originals) :
    models_over_tuple csp originals all_vertices (min_eo_encoding csp order) tuple =
      extension_count csp originals tuple :=
  models_over_tuple_eq_extension_count csp _ (min_eo_model_iff csp order tree_order) originals tuple

end parsimony
