import parsimony.rooted_orders
import parsimony.composition
import parsimony.orders_and_special_cases
import parsimony.size_and_minimality

namespace parsimony
namespace examples

open counterexamples

section second_start_example

def second_start_old_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 3, 3]
    [(0, 1, [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)]), (1, 2, [(0, 0), (1, 1), (2, 2)])] (by decide)
    (by decide)

def second_start_new_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 3] [(0, 1, [(0, 0), (1, 1)]), (1, 2, [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)])]
    (by decide) (by decide)

theorem second_start_extensions :
    is_tree_order second_start_old_csp [0, 1, 2] ∧ is_tree_order second_start_new_csp [0, 1, 2] ∧
      root_is_original (middle_vertex_is_hidden : Fin 3 → Bool) [0, 1, 2] ∧
      relation_count second_start_old_csp middle_vertex_is_hidden = 5 ∧
      has_unique_extension second_start_old_csp middle_vertex_is_hidden ∧
      relation_count second_start_new_csp middle_vertex_is_hidden = 5 ∧
      has_unique_extension second_start_new_csp middle_vertex_is_hidden := by
  decide +kernel

theorem second_start_same_relation :
    ∀ first : Fin 2, ∀ second : Fin 3,
      in_relation second_start_old_csp middle_vertex_is_hidden
        (tuple_of_values second_start_old_csp middle_vertex_is_hidden ![first.val, 0, second.val]) ↔
      in_relation second_start_new_csp middle_vertex_is_hidden
        (tuple_of_values second_start_new_csp middle_vertex_is_hidden ![first.val, 0, second.val]) := by
  decide +kernel

theorem second_start_every_value_on_a_solution :
    ∀ value : Fin (second_start_old_csp.domain_size 1), ∃ candidate : assignment second_start_old_csp,
      is_solution second_start_old_csp candidate ∧ candidate 1 = value := by
  decide +kernel

def second_start_pivot_first : neighbour_vertex second_start_old_csp 1 := ⟨0, by decide⟩

def second_start_pivot_second : neighbour_vertex second_start_old_csp 1 := ⟨2, by decide⟩

def second_start_box_a : neighbour_box second_start_old_csp 1 :=
  fun y => if y.val.val = 0 then Finset.univ.filter fun value => value.val = 0 else Finset.univ

def second_start_box_b : neighbour_box second_start_old_csp 1 :=
  fun y => if y.val.val = 0 then Finset.univ.filter fun value => value.val = 1
    else Finset.univ.filter fun value => value.val ≤ 1

theorem second_start_construction :
    second_start_old_csp.domain_size 0 < second_start_old_csp.domain_size 1 ∧
      second_start_old_csp.domain_size 0 ≤ second_start_old_csp.domain_size 2 ∧
      parsimony.merge_table second_start_old_csp 1 (parsimony.tuple_table second_start_old_csp 1)
        second_start_pivot_second = {second_start_box_a, second_start_box_b} ∧
      parsimony.merge_table second_start_old_csp 1 {second_start_box_a, second_start_box_b}
        second_start_pivot_first = {second_start_box_a, second_start_box_b} ∧
      parsimony.merge_table second_start_old_csp 1 {second_start_box_a, second_start_box_b}
        second_start_pivot_second = {second_start_box_a, second_start_box_b} := by
  decide +kernel

theorem second_start_new_is_the_reconstruction :
    (∀ first : Fin 2, ∀ value : Fin 2, second_start_new_csp.allowed 0 1 first value =
      decide (value.val = first.val)) ∧
    (∀ value : Fin 2, ∀ second : Fin 3, second_start_new_csp.allowed 1 2 value second =
      if value.val = 0 then true else decide (second.val ≤ 1)) := by
  decide +kernel

theorem second_start_old_minimal_support_counts :
    (∀ first : Fin 2, ∀ second : Fin 3, in_relation second_start_old_csp middle_vertex_is_hidden
        (tuple_of_values second_start_old_csp middle_vertex_is_hidden ![first.val, 0, second.val]) →
      models_over_tuple second_start_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding second_start_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values second_start_old_csp middle_vertex_is_hidden ![first.val, 0, second.val]) = 1) ∧
    model_count (minimal_support_encoding second_start_old_csp middle_vertex_is_hidden [0, 1, 2]) = 5 := by
  constructor
  · simp only [minimal_support_models_over_tuple_eq_selection_count]
    decide +kernel
  · decide +kernel

theorem second_start_new_minimal_support_counts :
    models_over_tuple second_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding second_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values second_start_new_csp middle_vertex_is_hidden ![0, 0, 0]) = 2 ∧
      models_over_tuple second_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding second_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values second_start_new_csp middle_vertex_is_hidden ![0, 0, 1]) = 2 ∧
      models_over_tuple second_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding second_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values second_start_new_csp middle_vertex_is_hidden ![0, 0, 2]) = 1 ∧
      models_over_tuple second_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding second_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values second_start_new_csp middle_vertex_is_hidden ![1, 0, 0]) = 2 ∧
      models_over_tuple second_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding second_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values second_start_new_csp middle_vertex_is_hidden ![1, 0, 1]) = 2 ∧
      model_count (minimal_support_encoding second_start_new_csp middle_vertex_is_hidden [0, 1, 2]) = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide +kernel⟩ <;>
  · simp only [minimal_support_models_over_tuple_eq_selection_count]
    decide +kernel

theorem second_start_sizes :
    evaluated_size second_start_old_csp = 15 ∧ evaluated_size second_start_new_csp = 10 := by
  decide +kernel

end second_start_example

section first_start_example

theorem first_start_totals :
    model_count (minimal_support_encoding ct_start_old_csp middle_vertex_is_hidden [0, 1, 2]) = 7 ∧
      model_count (minimal_support_encoding ct_start_new_csp middle_vertex_is_hidden [0, 1, 2]) = 9 := by
  decide +kernel

theorem first_start_rule_two_test :
    ct_start_old_csp.domain_size 0 * ct_start_old_csp.domain_size 2 = 6 ∧
      ct_start_old_csp.domain_size 1 *
        (ct_start_old_csp.domain_size 0 + ct_start_old_csp.domain_size 2) = 15 ∧
      ct_start_old_csp.domain_size 0 < ct_start_old_csp.domain_size 1 := by
  decide +kernel

theorem first_start_value_one_on_no_solution :
    ∀ candidate : assignment ct_start_old_csp, is_solution ct_start_old_csp candidate →
      (candidate 1).val ≠ 1 := by
  decide +kernel

end first_start_example

section rule_three_examples

theorem rule_three_full_is_the_merge :
    ∃ pair : Fin 4 → Fin 2 × Fin 2, Function.Bijective pair ∧
      (∀ first second : Fin 2, rule_three_full_csp.allowed 1 2 first second = true) ∧
      ∀ a : Fin 1, ∀ value : Fin 4, rule_three_full_merged_csp.allowed 0 1 a value =
        rule_three_full_csp.allowed 0 1 a (pair value).1 := by
  refine ⟨![(0, 0), (0, 1), (1, 0), (1, 1)], ?_, ?_, ?_⟩ <;> decide +kernel

theorem rule_three_copy_is_the_merge :
    ∃ pair : Fin 2 → Fin 2 × Fin 2, Function.Injective pair ∧
      (∀ first second : Fin 2, rule_three_copy_csp.allowed 1 2 first second = true ↔
        ∃ value, pair value = (first, second)) ∧
      ∀ a : Fin 1, ∀ value : Fin 2, rule_three_copy_merged_csp.allowed 0 1 a value =
        rule_three_copy_csp.allowed 0 1 a (pair value).1 := by
  refine ⟨![(0, 0), (1, 1)], ?_, ?_, ?_⟩ <;> decide +kernel

theorem rule_three_copy_upward_sets
    (tuple : original_tuple rule_three_copy_csp first_vertex_is_original) :
    (∀ value : Fin (rule_three_copy_csp.domain_size 2),
      in_upward_set rule_three_copy_csp first_vertex_is_original [0, 1, 2] tuple 2 value) ∧
    ∀ value : Fin (rule_three_copy_csp.domain_size 1),
      in_upward_set rule_three_copy_csp first_vertex_is_original [0, 1, 2] tuple 1 value := by
  have last : ∀ value : Fin (rule_three_copy_csp.domain_size 2),
      in_upward_set rule_three_copy_csp first_vertex_is_original [0, 1, 2] tuple 2 value := fun value =>
    hidden_leaf_upward_set_is_domain rule_three_copy_csp first_vertex_is_original [0, 1, 2] tuple 2
      (by decide) (by decide +kernel) value
  refine ⟨last, fun value => ?_⟩
  rw [in_upward_set_iff]
  refine ⟨fun on_h => absurd on_h (by decide), fun y adjacent_h_y h_earlier => ?_⟩
  have witness : ∀ a : Fin (rule_three_copy_csp.domain_size 1), ∀ z : Fin 3,
      rule_three_copy_csp.adjacent 1 z = true → earlier_in [0, 1, 2] (1 : Fin 3) z = true →
        z = 2 ∧ ∃ b : Fin (rule_three_copy_csp.domain_size 2),
          rule_three_copy_csp.allowed 1 2 a b = true := by
    decide +kernel
  obtain ⟨rfl, b, allowed⟩ := witness value y adjacent_h_y h_earlier
  exact ⟨b, allowed, last b⟩

theorem rule_three_copy_product_is_not_the_count :
    2 ^ (rule_three_copy_csp.domain_size 1 - 1) * 2 ^ (rule_three_copy_csp.domain_size 2 - 1) = 4 ∧
      model_count (minimal_support_encoding rule_three_copy_csp first_vertex_is_original [0, 1, 2]) = 3 := by
  decide +kernel

end rule_three_examples

section rule_four_examples

theorem rule_four_partition_boxes :
    (∀ first second : Fin 2, (Finset.univ.filter fun value : Fin 3 =>
      rule_four_partition_old_csp.allowed 0 1 first value = true ∧
        rule_four_partition_old_csp.allowed 1 2 value second = true).card = 1) ∧
    ∀ first second : Fin 2, (Finset.univ.filter fun value : Fin 2 =>
      rule_four_partition_new_csp.allowed 0 1 first value = true ∧
        rule_four_partition_new_csp.allowed 1 2 value second = true).card = 1 := by
  decide +kernel

theorem rule_four_partition_totals :
    model_count (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden
        [0, 1, 2]) = 6 ∧
      model_count (minimal_support_encoding rule_four_partition_new_csp middle_vertex_is_hidden
        [0, 1, 2]) = 8 := by
  decide +kernel

def rule_four_new_csp : binary_csp 2 :=
  csp_of_edges 2 [2, 2] [(0, 1, [(0, 0), (0, 1), (1, 1)])] (by decide) (by decide)

theorem rule_four_example_sizes :
    evaluated_size rule_four_csp = 2 ∧ evaluated_size rule_four_new_csp = 4 ∧
      evaluated_size rule_four_small_csp = 9 ∧ evaluated_size rule_four_small_new_csp = 6 ∧
      extension_count rule_four_new_csp first_vertex_is_original
        (tuple_of_values rule_four_new_csp first_vertex_is_original ![0, 0]) = 2 ∧
      extension_count rule_four_new_csp first_vertex_is_original
        (tuple_of_values rule_four_new_csp first_vertex_is_original ![1, 0]) = 1 := by
  decide +kernel

end rule_four_examples

section merge_remark

def literal_box_a : Finset (ℕ × ℕ) := {(0, 0), (1, 0)}

def literal_box_b : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (1, 1)}

theorem merge_remark_literal_sets :
    (∀ literal ∈ literal_box_a \ literal_box_b, literal.1 = 1) ∧
      ¬ (∀ literal ∈ literal_box_b \ literal_box_a, literal.1 = 1) ∧
      ((0, 1) ∈ literal_box_a ∪ literal_box_b ∧ (1, 0) ∈ literal_box_a ∪ literal_box_b) ∧
      ¬ ((0, 1) ∈ literal_box_a ∧ (1, 0) ∈ literal_box_a) ∧
      ¬ ((0, 1) ∈ literal_box_b ∧ (1, 0) ∈ literal_box_b) ∧
      ∀ first second : Fin 2, ((0, first.val) ∈ literal_box_a ∪ literal_box_b ∧
        (1, second.val) ∈ literal_box_a ∪ literal_box_b) ∧
        ((((0, first.val) ∈ literal_box_a ∧ (1, second.val) ∈ literal_box_a) ∨
          ((0, first.val) ∈ literal_box_b ∧ (1, second.val) ∈ literal_box_b)) ↔
            ¬ (first.val = 1 ∧ second.val = 0)) := by
  decide +kernel

theorem contained_union (first second : Finset (ℕ × ℕ)) (contained : first ⊆ second) :
    first ∪ second = second :=
  Finset.union_eq_right.mpr contained

def contained_or_agree (pivot : ℕ) (first second : Finset (ℕ × ℕ)) : Prop :=
  first ⊆ second ∨ second ⊆ first ∨
    ((∀ literal ∈ first \ second, literal.1 = pivot) ∧ ∀ literal ∈ second \ first, literal.1 = pivot)

instance (pivot : ℕ) (first second : Finset (ℕ × ℕ)) : Decidable (contained_or_agree pivot first second) := by
  unfold contained_or_agree
  infer_instance

theorem contained_or_agree_is_not_transitive :
    ∃ first second third : Finset (ℕ × ℕ), ∀ pivot : Fin 2,
      contained_or_agree pivot first second ∧ contained_or_agree pivot second third ∧
        ¬ contained_or_agree pivot first third :=
  ⟨{(0, 0), (1, 0)}, {(0, 0), (0, 1), (1, 0), (1, 1)}, {(0, 1), (1, 1)}, by decide +kernel⟩

end merge_remark

section layered_examples

def two_labels_mdd : layered_mdd 2 where
  symbol_count := fun _ => 2
  node_count := fun layer => if layer.val = 1 then 2 else 1
  edge_count := fun _ => 2
  edge_source := fun layer edge => if h : layer.val = 1 then ⟨edge.val, by simp [h]; omega⟩ else
    ⟨0, by
      simp [h]⟩
  edge_target := fun layer edge => if h : layer.val = 0 then ⟨edge.val, by simp [h]; omega⟩ else
    ⟨0, by
      simp [h]⟩
  edge_label := fun layer edge => if layer.val = 0 then 0 else edge

theorem two_labels_mdd_not_deterministic : ¬ is_deterministic_mdd two_labels_mdd := by
  unfold is_deterministic_mdd
  decide +kernel

theorem two_labels_mdd_at_most_one_path :
    ∀ word, mdd_dtbe_extension_count two_labels_mdd word ≤ 1 := by
  decide +kernel

theorem two_labels_mdd_accepts_two_words :
    mdd_dtbe_extension_count two_labels_mdd (fun _ => ⟨0, Nat.zero_lt_two⟩) = 1 ∧
      mdd_dtbe_extension_count two_labels_mdd (fun layer => ⟨if layer.val = 0 then 0 else 1, by
        show (if layer.val = 0 then 0 else 1) < 2
        split <;> decide⟩) = 1 := by
  decide +kernel

end layered_examples

section smallest_examples

theorem one_vertex_minimal_support_parsimonious (csp : binary_csp 1) (originals : Fin 1 → Bool)
    (order : List (Fin 1)) (tree_order : is_tree_order csp order)
    (root_original : root_is_original originals order) :
    is_parsimonious csp originals (minimal_support_encoding csp originals order) := by
  rw [minimal_support_parsimonious_iff csp originals order tree_order root_original]
  intro tuple _ h h_hidden
  obtain ⟨root, _, root_on⟩ := root_original
  have same : root = h := Subsingleton.elim root h
  rw [same, h_hidden] at root_on
  exact absurd root_on (by decide)

theorem singleton_hidden_unique_extension {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool)
    (singleton_hidden : ∀ h, originals h = false → csp.domain_size h = 1) :
    has_unique_extension csp originals := by
  rintro tuple ⟨candidate, solution, restricted⟩
  unfold extension_count
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨candidate, solution, restricted⟩, ?_⟩
  rintro ⟨other, other_solution, other_restricted⟩
  apply Subtype.ext
  funext x
  by_cases on_x : originals x = true
  · exact congrFun (other_restricted.trans restricted.symm) ⟨x, on_x⟩
  · have domain_one := singleton_hidden x (by simpa using on_x)
    apply Fin.ext
    have other_lt := (other x).isLt
    have candidate_lt := (candidate x).isLt
    omega

theorem all_original_roots_agree {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (first second : List (Fin vertex_count)) (first_order : is_tree_order csp first)
    (second_order : is_tree_order csp second) :
    model_count (minimal_support_encoding csp all_vertices first) =
      model_count (minimal_support_encoding csp all_vertices second) := by
  have first_count := (all_six_parsimonious_without_hidden csp first first_order).2.2.2.2.2
  have second_count := (all_six_parsimonious_without_hidden csp second second_order).2.2.2.2.2
  exact first_count.trans second_count.symm

theorem singleton_hidden_roots_agree {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (first second : List (Fin vertex_count))
    (first_order : is_tree_order csp first) (second_order : is_tree_order csp second)
    (first_root : root_is_original originals first) (second_root : root_is_original originals second)
    (singleton_hidden : ∀ h, originals h = false → csp.domain_size h = 1) :
    model_count (minimal_support_encoding csp originals first) =
      model_count (minimal_support_encoding csp originals second) := by
  have first_count := minimal_support_parsimonious_of_singleton_hidden_domains csp originals first
    first_order first_root singleton_hidden
  have second_count := minimal_support_parsimonious_of_singleton_hidden_domains csp originals second
    second_order second_root singleton_hidden
  exact first_count.trans second_count.symm

theorem two_vertex_orders_are_tree_orders (csp : binary_csp 2) (tree : is_binary_constraint_tree csp) :
    is_tree_order csp [0, 1] ∧ is_tree_order csp [1, 0] := by
  have joined : csp.adjacent 0 1 = true := by
    have connected := tree.1
    obtain ⟨walk⟩ := connected.preconnected 0 1
    cases walk with
    | cons adjacent_step later_walk =>
      rename_i middle
      have adjacent_middle : csp.adjacent 0 middle = true := adjacent_step
      have middle_is : middle = 0 ∨ middle = 1 := by omega
      rcases middle_is with rfl | rfl
      · rw [csp.adjacent_irrefl] at adjacent_middle
        exact absurd adjacent_middle (by decide)
      · exact adjacent_middle
  have joined_back : csp.adjacent 1 0 = true := by rw [csp.adjacent_symm]; exact joined
  constructor
  · refine ⟨by decide, by decide, fun later later_pos => ?_⟩
    have below : later.val < 2 := later.isLt
    have later_is : later = ⟨1, by decide⟩ := by
      apply Fin.ext
      show later.val = 1
      omega
    subst later_is
    simp [joined]
  · refine ⟨by decide, by decide, fun later later_pos => ?_⟩
    have below : later.val < 2 := later.isLt
    have later_is : later = ⟨1, by decide⟩ := by
      apply Fin.ext
      show later.val = 1
      omega
    subst later_is
    simp [joined_back]

end smallest_examples

section nfa_example_after_rules

def two_run_after_rule_one_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 2] [(0, 1, [(0, 0), (0, 1)])] (by decide) (by decide)

def two_run_pivot : neighbour_vertex two_run_after_rule_one_csp 1 := ⟨0, by decide⟩

theorem two_run_after_rule_one_boxes :
    (parsimony.value_table two_run_after_rule_one_csp 1).card = 1 ∧
      (parsimony.merge_table two_run_after_rule_one_csp 1
        (parsimony.tuple_table two_run_after_rule_one_csp 1) two_run_pivot).card = 1 ∧
      reconstructed_extension_count two_run_after_rule_one_csp first_vertex_is_original 1
        (parsimony.merge_table two_run_after_rule_one_csp 1
          (parsimony.tuple_table two_run_after_rule_one_csp 1) two_run_pivot)
        (tuple_of_values two_run_after_rule_one_csp first_vertex_is_original ![0, 0]) = 1 ∧
      eliminated_extension_count two_run_after_rule_one_csp first_vertex_is_original 1
        (tuple_of_values two_run_after_rule_one_csp first_vertex_is_original ![0, 0]) = 1 := by
  decide +kernel

end nfa_example_after_rules

section several_constraints

theorem conjunction_not_parsimonious_of_independent_part {original_count : ℕ}
    (problem : composition_problem original_count 2) (covers : covers_all_originals problem)
    (exact : ∀ part, part_is_projection_exact problem part)
    (injective : ∀ part, Function.Injective (problem.scope_original part))
    (disjoint : ∀ first second, problem.scope_original 0 first ≠ problem.scope_original 1 second)
    (first_tuple : part_tuple problem 0) (first_tuple_relation : problem.part_relation 0 first_tuple)
    (first_tuple_count : part_models_over problem 0 first_tuple ≠ 1) (other : part_tuple problem 1)
    (other_relation : problem.part_relation 1 other) :
    model_count (conjunction_formula problem) ≠
      (Finset.univ.filter (satisfies_all_parts problem)).card := by
  classical
  intro parsimonious
  rw [composition_parsimonious_iff problem covers exact] at parsimonious
  have built : ∀ original, ∃ value : Fin (problem.domain_size original),
      (∀ member (same : problem.scope_original 0 member = original), same ▸ first_tuple member = value) ∧
      ∀ member (same : problem.scope_original 1 member = original), same ▸ other member = value := by
    intro original
    obtain ⟨part, member, rfl⟩ := covers original
    have part_is : part = 0 ∨ part = 1 := by omega
    rcases part_is with rfl | rfl
    · refine ⟨first_tuple member, fun first same => ?_, fun second same => absurd same.symm (disjoint member second)⟩
      have same_member := injective 0 same
      subst same_member
      rfl
    · refine ⟨other member, fun first same => absurd same (disjoint first member), fun second same => ?_⟩
      have same_member := injective 1 same
      subst same_member
      rfl
  choose tuple from_first_tuple from_other using built
  have first_restrict : restrict_to_part problem tuple 0 = first_tuple := by
    funext member
    exact (from_first_tuple _ member rfl).symm
  have second_restrict : restrict_to_part problem tuple 1 = other := by
    funext member
    exact (from_other _ member rfl).symm
  have satisfied : satisfies_all_parts problem tuple := by
    intro part
    have part_is : part = 0 ∨ part = 1 := by omega
    rcases part_is with rfl | rfl
    · rw [first_restrict]
      exact first_tuple_relation
    · rw [second_restrict]
      exact other_relation
  have one := parsimonious tuple satisfied 0
  rw [first_restrict] at one
  exact first_tuple_count one

end several_constraints

end examples
end parsimony
