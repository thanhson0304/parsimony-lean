import parsimony.minimal_support_counting
import parsimony.descent

namespace parsimony

variable {vertex_count : ℕ}

theorem head_of_index_zero (order : List (Fin vertex_count)) (x : Fin vertex_count)
    (x_mem : x ∈ order) (index_zero : order.idxOf x = 0) : order.head? = some x := by
  cases order with
  | nil => exact absurd x_mem (by simp)
  | cons first rest =>
    by_cases first_is : first = x
    · rw [first_is]
      rfl
    · rw [List.idxOf_cons] at index_zero
      simp [first_is] at index_zero

theorem earlier_in_first_implies_second (csp : binary_csp vertex_count)
    (first second : List (Fin vertex_count)) (first_order : is_tree_order csp first)
    (second_order : is_tree_order csp second) (same_head : first.head? = second.head?) :
    ∀ x y, csp.adjacent x y = true → earlier_in first x y = true →
      earlier_in second x y = true := by
  have claim : ∀ position, ∀ y, first.idxOf y = position → ∀ x, csp.adjacent x y = true →
      earlier_in first x y = true → earlier_in second x y = true := by
    intro position
    induction position using Nat.strong_induction_on with
    | _ position induction_step =>
      intro y y_position x adjacent_x_y first_earlier
      by_contra not_second
      have second_later : earlier_in second y x = true := by
        rcases earlier_or_later csp second second_order x y adjacent_x_y with x_first | y_first
        · exact absurd x_first not_second
        · exact y_first
      have x_before_y : first.idxOf x < first.idxOf y := by
        simpa [earlier_in] using first_earlier
      by_cases x_root : first.idxOf x = 0
      · have head_x := head_of_index_zero first x (first_order.2.1 x) x_root
        rw [same_head] at head_x
        have second_zero := index_zero_of_head second x head_x
        have y_before_x : second.idxOf y < second.idxOf x := by
          simpa [earlier_in] using second_later
        omega
      · obtain ⟨parent, parent_adjacent, parent_before, _⟩ :=
          tree_order_unique_earlier_neighbour csp first first_order x (by omega)
        have parent_second : earlier_in second parent x = true :=
          induction_step (first.idxOf x) (by omega) x rfl parent parent_adjacent
            (by simpa [earlier_in] using parent_before)
        have y_adjacent_x : csp.adjacent y x = true := by
          rw [csp.adjacent_symm]
          exact adjacent_x_y
        have y_is_parent : y = parent :=
          earlier_neighbour_unique csp second second_order x y parent y_adjacent_x second_later
            parent_adjacent parent_second
        rw [y_is_parent] at x_before_y
        omega
  intro x y adjacent_x_y first_earlier
  exact claim (first.idxOf y) y rfl x adjacent_x_y first_earlier

theorem tree_orders_with_same_root_agree (csp : binary_csp vertex_count)
    (first second : List (Fin vertex_count)) (first_order : is_tree_order csp first)
    (second_order : is_tree_order csp second) (same_head : first.head? = second.head?)
    (x y : Fin vertex_count) (adjacent_x_y : csp.adjacent x y = true) :
    earlier_in first x y = earlier_in second x y := by
  cases first_value : earlier_in first x y
  · rcases earlier_or_later csp first first_order x y adjacent_x_y with x_first | y_first
    · rw [first_value] at x_first
      exact absurd x_first (by decide)
    · have y_second := earlier_in_first_implies_second csp first second first_order second_order
        same_head y x (by rw [csp.adjacent_symm]; exact adjacent_x_y) y_first
      have y_before : second.idxOf y < second.idxOf x := by simpa [earlier_in] using y_second
      symm
      simp only [earlier_in, decide_eq_false_iff_not]
      omega
  · exact (earlier_in_first_implies_second csp first second first_order second_order same_head
      x y adjacent_x_y first_value).symm

theorem tree_order_support_clauses_same_root (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (first second : List (Fin vertex_count))
    (first_order : is_tree_order csp first) (second_order : is_tree_order csp second)
    (same_head : first.head? = second.head?) :
    tree_order_support_clauses csp ladder_on first =
      tree_order_support_clauses csp ladder_on second := by
  unfold tree_order_support_clauses
  have chosen_eq : (fun x y => csp.adjacent x y && earlier_in first x y) =
      (fun x y => csp.adjacent x y && earlier_in second x y) := by
    funext x y
    cases adjacent_value : csp.adjacent x y
    · rfl
    · simp only [Bool.true_and]
      exact tree_orders_with_same_root_agree csp first second first_order second_order same_head
        x y adjacent_value
  rw [chosen_eq]

theorem minimal_support_encoding_same_root (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (first second : List (Fin vertex_count))
    (first_order : is_tree_order csp first) (second_order : is_tree_order csp second)
    (same_head : first.head? = second.head?) :
    minimal_support_encoding csp originals first = minimal_support_encoding csp originals second := by
  unfold minimal_support_encoding
  rw [tree_order_support_clauses_same_root csp originals first second first_order second_order
    same_head]

theorem min_eo_encoding_same_root (csp : binary_csp vertex_count)
    (first second : List (Fin vertex_count))
    (first_order : is_tree_order csp first) (second_order : is_tree_order csp second)
    (same_head : first.head? = second.head?) :
    min_eo_encoding csp first = min_eo_encoding csp second := by
  unfold min_eo_encoding
  rw [tree_order_support_clauses_same_root csp all_vertices first second first_order second_order
    same_head]

theorem no_hidden_has_unique_extension (csp : binary_csp vertex_count) :
    has_unique_extension csp all_vertices := by
  intro tuple in_rel
  rw [extension_count_eq_one_iff]
  obtain ⟨candidate, solution, restricted⟩ := in_rel
  refine ⟨candidate, ⟨solution, restricted⟩, ?_⟩
  rintro other ⟨_, other_restricted⟩
  funext x
  exact (congrFun other_restricted ⟨x, rfl⟩).trans (congrFun restricted ⟨x, rfl⟩).symm

theorem partial_support_without_hidden_is_support (csp : binary_csp vertex_count) :
    partial_support_encoding csp all_vertices = support_encoding csp := rfl

theorem minimal_support_without_hidden_is_min_eo (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) :
    minimal_support_encoding csp all_vertices order = min_eo_encoding csp order := rfl

theorem all_six_parsimonious_without_hidden (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order) :
    is_parsimonious csp all_vertices (support_encoding csp) ∧
      is_parsimonious csp all_vertices (direct_encoding csp) ∧
      is_parsimonious csp all_vertices (log_encoding csp) ∧
      is_parsimonious csp all_vertices (min_eo_encoding csp order) ∧
      is_parsimonious csp all_vertices (partial_support_encoding csp all_vertices) ∧
      is_parsimonious csp all_vertices (minimal_support_encoding csp all_vertices order) := by
  have unique := no_hidden_has_unique_extension csp
  exact ⟨(support_parsimonious_iff csp all_vertices).mpr unique,
    (direct_parsimonious_iff csp all_vertices).mpr unique,
    (log_parsimonious_iff csp all_vertices).mpr unique,
    (min_eo_parsimonious_iff csp all_vertices order tree_order).mpr unique,
    (support_parsimonious_iff csp all_vertices).mpr unique,
    (min_eo_parsimonious_iff csp all_vertices order tree_order).mpr unique⟩

theorem model_count_zero_of_empty_relation (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (formula : cnf_formula (boolean_variable csp ladder_on))
    (projection_exact : is_projection_exact csp originals ladder_on formula)
    (empty_relation : ∀ tuple, ¬ in_relation csp originals tuple) :
    model_count formula = 0 := by
  unfold model_count
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun valuation => ?_⟩
  obtain ⟨tuple, in_rel, _⟩ := projection_exact.1 valuation.val valuation.property
  exact empty_relation tuple in_rel

theorem log_model_count_zero_of_empty_relation (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool)
    (empty_relation : ∀ tuple, ¬ in_relation csp originals tuple) :
    model_count (log_encoding csp) = 0 := by
  unfold model_count
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun valuation => ?_⟩
  obtain ⟨tuple, in_rel, _⟩ :=
    (log_is_projection_exact_theorem csp originals).1 valuation.val valuation.property
  exact empty_relation tuple in_rel

end parsimony
