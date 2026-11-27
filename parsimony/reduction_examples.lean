import parsimony.base_examples

namespace parsimony

variable {vertex_count : ℕ}

def tuple_of_values (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (values : Fin vertex_count → ℕ) : original_tuple csp originals :=
  fun x => ⟨values x.val % csp.domain_size x.val, Nat.mod_lt _ (csp.domain_nonempty x.val)⟩

namespace counterexamples

theorem rule_one_smallest_decrease :
    extension_count two_extensions_csp first_vertex_is_original
        (tuple_of_values two_extensions_csp first_vertex_is_original ![0, 0]) = 2 ∧
      eliminated_extension_count two_extensions_csp first_vertex_is_original 1
        (tuple_of_values two_extensions_csp first_vertex_is_original ![0, 0]) = 1 := by
  decide +kernel

def rule_two_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 1] [(0, 1, [(0, 0), (0, 1)]), (1, 2, [(0, 0), (1, 0)])] (by decide)
    (by decide)

theorem rule_two_smallest_decrease :
    extension_count rule_two_csp middle_vertex_is_hidden
        (tuple_of_values rule_two_csp middle_vertex_is_hidden ![0, 0, 0]) = 2 ∧
      eliminated_extension_count rule_two_csp middle_vertex_is_hidden 1
        (tuple_of_values rule_two_csp middle_vertex_is_hidden ![0, 0, 0]) = 1 := by
  decide +kernel

def rule_four_csp : binary_csp 2 :=
  csp_of_edges 2 [2, 1] [(0, 1, [(0, 0), (1, 0)])] (by decide) (by decide)

def rule_four_box_a : neighbour_box rule_four_csp 1 :=
  fun _ => Finset.univ.filter fun value => value.val = 0

def rule_four_box_b : neighbour_box rule_four_csp 1 :=
  fun _ => Finset.univ

theorem rule_four_table_is_valid :
    is_valid_cc_table rule_four_csp 1 {rule_four_box_a, rule_four_box_b} := by
  unfold is_valid_cc_table
  decide +kernel

theorem rule_four_breaks_uniqueness :
    has_unique_extension rule_four_csp first_vertex_is_original ∧
      reconstructed_extension_count rule_four_csp first_vertex_is_original 1
        {rule_four_box_a, rule_four_box_b}
        (tuple_of_values rule_four_csp first_vertex_is_original ![0, 0]) = 2 ∧
      reconstructed_extension_count rule_four_csp first_vertex_is_original 1
        {rule_four_box_a, rule_four_box_b}
        (tuple_of_values rule_four_csp first_vertex_is_original ![1, 0]) = 1 := by
  decide +kernel

def rule_four_small_csp : binary_csp 2 :=
  csp_of_edges 2 [3, 3] [(0, 1, [(0, 0), (1, 1), (2, 2)])] (by decide) (by decide)

def rule_four_low_box : neighbour_box rule_four_small_csp 1 :=
  fun _ => Finset.univ.filter fun value => value.val ≤ 1

def rule_four_high_box : neighbour_box rule_four_small_csp 1 :=
  fun _ => Finset.univ.filter fun value => 1 ≤ value.val

theorem rule_four_small_table_is_valid :
    is_valid_cc_table rule_four_small_csp 1 {rule_four_low_box, rule_four_high_box} := by
  unfold is_valid_cc_table
  decide +kernel

theorem rule_four_small_counts :
    has_unique_extension rule_four_small_csp first_vertex_is_original ∧
      reconstructed_extension_count rule_four_small_csp first_vertex_is_original 1
        {rule_four_low_box, rule_four_high_box}
        (tuple_of_values rule_four_small_csp first_vertex_is_original ![0, 0]) = 1 ∧
      reconstructed_extension_count rule_four_small_csp first_vertex_is_original 1
        {rule_four_low_box, rule_four_high_box}
        (tuple_of_values rule_four_small_csp first_vertex_is_original ![1, 0]) = 2 ∧
      reconstructed_extension_count rule_four_small_csp first_vertex_is_original 1
        {rule_four_low_box, rule_four_high_box}
        (tuple_of_values rule_four_small_csp first_vertex_is_original ![2, 0]) = 1 := by
  decide +kernel

def merge_remark_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 1, 2] [(0, 1, [(0, 0), (1, 0)]), (1, 2, [(0, 0), (0, 1)])] (by decide)
    (by decide)

def merge_remark_box_a : neighbour_box merge_remark_csp 1 :=
  fun _ => Finset.univ.filter fun value => value.val = 0

def merge_remark_box_b : neighbour_box merge_remark_csp 1 :=
  fun y => if y.val.val = 0 then Finset.univ else Finset.univ.filter fun value => value.val = 1

def merge_remark_union : neighbour_box merge_remark_csp 1 :=
  fun y => merge_remark_box_a y ∪ merge_remark_box_b y

theorem merge_remark_union_represents_new_tuple :
    ∃ neighbours, box_represents merge_remark_csp 1 merge_remark_union neighbours ∧
      ¬ box_represents merge_remark_csp 1 merge_remark_box_a neighbours ∧
      ¬ box_represents merge_remark_csp 1 merge_remark_box_b neighbours := by
  decide +kernel

theorem merge_remark_boxes_never_agree_outside :
    ∀ pivot, ¬ agree_outside merge_remark_csp 1 pivot merge_remark_box_a merge_remark_box_b := by
  decide +kernel

def rule_three_full_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 2] [(0, 1, [(0, 0), (0, 1)]), (1, 2, [(0, 0), (0, 1), (1, 0), (1, 1)])]
    (by decide) (by decide)

def rule_three_full_merged_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 4] [(0, 1, [(0, 0), (0, 1), (0, 2), (0, 3)])] (by decide) (by decide)

theorem rule_three_full_counts :
    is_tree_order rule_three_full_csp [0, 1, 2] ∧
      is_tree_order rule_three_full_merged_csp [0, 1] ∧
      model_count (minimal_support_encoding rule_three_full_csp first_vertex_is_original
        [0, 1, 2]) = 9 ∧
      model_count (minimal_support_encoding rule_three_full_merged_csp first_vertex_is_original
        [0, 1]) = 15 := by
  decide +kernel

def rule_three_copy_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 2] [(0, 1, [(0, 0)]), (1, 2, [(0, 0), (1, 1)])] (by decide) (by decide)

def rule_three_copy_merged_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 2] [(0, 1, [(0, 0)])] (by decide) (by decide)

theorem rule_three_copy_counts :
    is_tree_order rule_three_copy_csp [0, 1, 2] ∧
      is_tree_order rule_three_copy_merged_csp [0, 1] ∧
      has_unique_extension rule_three_copy_csp first_vertex_is_original ∧
      model_count (minimal_support_encoding rule_three_copy_csp first_vertex_is_original
        [0, 1, 2]) = 3 ∧
      model_count (minimal_support_encoding rule_three_copy_merged_csp first_vertex_is_original
        [0, 1]) = 2 := by
  decide +kernel

def rule_four_partition_old_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 3, 2]
    [(0, 1, [(0, 0), (1, 0), (0, 1), (1, 2)]), (1, 2, [(0, 0), (1, 1), (2, 1)])] (by decide)
    (by decide)

def rule_four_partition_new_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 2] [(0, 1, [(0, 0), (1, 1)]), (1, 2, [(0, 0), (0, 1), (1, 0), (1, 1)])]
    (by decide) (by decide)

theorem rule_four_partition_extensions :
    is_tree_order rule_four_partition_old_csp [0, 1, 2] ∧
      is_tree_order rule_four_partition_new_csp [0, 1, 2] ∧
      relation_count rule_four_partition_old_csp middle_vertex_is_hidden = 4 ∧
      has_unique_extension rule_four_partition_old_csp middle_vertex_is_hidden ∧
      relation_count rule_four_partition_new_csp middle_vertex_is_hidden = 4 ∧
      has_unique_extension rule_four_partition_new_csp middle_vertex_is_hidden := by
  decide +kernel

theorem rule_four_partition_old_counts :
    models_over_tuple rule_four_partition_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_old_csp middle_vertex_is_hidden ![0, 0, 0]) = 1 ∧
      models_over_tuple rule_four_partition_old_csp middle_vertex_is_hidden
        middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_old_csp middle_vertex_is_hidden ![0, 0, 1]) = 2 ∧
      models_over_tuple rule_four_partition_old_csp middle_vertex_is_hidden
        middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_old_csp middle_vertex_is_hidden ![1, 0, 0]) = 1 ∧
      models_over_tuple rule_four_partition_old_csp middle_vertex_is_hidden
        middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_old_csp middle_vertex_is_hidden ![1, 0, 1]) = 2 := by
  simp only [minimal_support_models_over_tuple_eq_selection_count]
  decide +kernel

theorem rule_four_partition_new_counts :
    models_over_tuple rule_four_partition_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_new_csp middle_vertex_is_hidden ![0, 0, 0]) = 2 ∧
      models_over_tuple rule_four_partition_new_csp middle_vertex_is_hidden
        middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_new_csp middle_vertex_is_hidden ![0, 0, 1]) = 2 ∧
      models_over_tuple rule_four_partition_new_csp middle_vertex_is_hidden
        middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_new_csp middle_vertex_is_hidden ![1, 0, 0]) = 2 ∧
      models_over_tuple rule_four_partition_new_csp middle_vertex_is_hidden
        middle_vertex_is_hidden
        (minimal_support_encoding rule_four_partition_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values rule_four_partition_new_csp middle_vertex_is_hidden ![1, 0, 1]) = 2 := by
  simp only [minimal_support_models_over_tuple_eq_selection_count]
  decide +kernel

def rule_four_small_new_csp : binary_csp 2 :=
  csp_of_edges 2 [3, 2] [(0, 1, [(0, 0), (1, 0), (1, 1), (2, 1)])] (by decide) (by decide)

theorem rule_four_small_minimal_support_counts :
    is_tree_order rule_four_small_csp [0, 1] ∧
      is_tree_order rule_four_small_new_csp [0, 1] ∧
      model_count (minimal_support_encoding rule_four_small_csp first_vertex_is_original
        [0, 1]) = 12 ∧
      model_count (minimal_support_encoding rule_four_small_new_csp first_vertex_is_original
        [0, 1]) = 7 ∧
      relation_count rule_four_small_new_csp first_vertex_is_original = 3 ∧
      extension_count rule_four_small_new_csp first_vertex_is_original
        (tuple_of_values rule_four_small_new_csp first_vertex_is_original ![1, 0]) = 2 := by
  decide +kernel

def ct_start_old_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 3, 3]
    [(0, 1, [(0, 0), (1, 0), (1, 2)]), (1, 2, [(0, 0), (0, 2), (1, 2), (2, 1)])] (by decide)
    (by decide)

def ct_start_new_csp : binary_csp 3 :=
  csp_of_edges 3 [2, 2, 3]
    [(0, 1, [(0, 0), (1, 1)]), (1, 2, [(0, 0), (0, 2), (1, 0), (1, 1), (1, 2)])] (by decide)
    (by decide)

theorem ct_start_extensions :
    is_tree_order ct_start_old_csp [0, 1, 2] ∧ is_tree_order ct_start_new_csp [0, 1, 2] ∧
      relation_count ct_start_old_csp middle_vertex_is_hidden = 5 ∧
      has_unique_extension ct_start_old_csp middle_vertex_is_hidden ∧
      relation_count ct_start_new_csp middle_vertex_is_hidden = 5 ∧
      has_unique_extension ct_start_new_csp middle_vertex_is_hidden ∧
      ∀ candidate : assignment ct_start_old_csp, is_solution ct_start_old_csp candidate →
        (candidate 1).val ≠ 1 := by
  decide +kernel

def ct_start_pivot_first : neighbour_vertex ct_start_old_csp 1 := ⟨0, by decide⟩

def ct_start_pivot_second : neighbour_vertex ct_start_old_csp 1 := ⟨2, by decide⟩

def ct_start_box_a : neighbour_box ct_start_old_csp 1 :=
  fun y => if y.val.val = 0 then Finset.univ.filter (fun value => value.val = 0)
    else Finset.univ.filter (fun value => value.val ≠ 1)

def ct_start_box_b : neighbour_box ct_start_old_csp 1 :=
  fun y => if y.val.val = 0 then Finset.univ.filter (fun value => value.val = 1) else Finset.univ

theorem ct_start_construction :
    merge_table ct_start_old_csp 1 (tuple_table ct_start_old_csp 1) ct_start_pivot_second =
        {ct_start_box_a, ct_start_box_b} ∧
      merge_table ct_start_old_csp 1 {ct_start_box_a, ct_start_box_b} ct_start_pivot_first =
        {ct_start_box_a, ct_start_box_b} ∧
      merge_table ct_start_old_csp 1 {ct_start_box_a, ct_start_box_b} ct_start_pivot_second =
        {ct_start_box_a, ct_start_box_b} := by
  decide +kernel

theorem ct_start_table_keeps_one_extension :
    reconstructed_extension_count ct_start_old_csp middle_vertex_is_hidden 1
        {ct_start_box_a, ct_start_box_b}
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![0, 0, 0]) = 1 ∧
      reconstructed_extension_count ct_start_old_csp middle_vertex_is_hidden 1
        {ct_start_box_a, ct_start_box_b}
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![0, 0, 2]) = 1 ∧
      reconstructed_extension_count ct_start_old_csp middle_vertex_is_hidden 1
        {ct_start_box_a, ct_start_box_b}
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![1, 0, 0]) = 1 ∧
      reconstructed_extension_count ct_start_old_csp middle_vertex_is_hidden 1
        {ct_start_box_a, ct_start_box_b}
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![1, 0, 1]) = 1 ∧
      reconstructed_extension_count ct_start_old_csp middle_vertex_is_hidden 1
        {ct_start_box_a, ct_start_box_b}
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![1, 0, 2]) = 1 := by
  decide +kernel

theorem ct_start_old_minimal_support_counts :
    models_over_tuple ct_start_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![0, 0, 0]) = 1 ∧
      models_over_tuple ct_start_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![0, 0, 2]) = 2 ∧
      models_over_tuple ct_start_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![1, 0, 0]) = 1 ∧
      models_over_tuple ct_start_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![1, 0, 1]) = 1 ∧
      models_over_tuple ct_start_old_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_old_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_old_csp middle_vertex_is_hidden ![1, 0, 2]) = 2 := by
  simp only [minimal_support_models_over_tuple_eq_selection_count]
  decide +kernel

theorem ct_start_new_minimal_support_counts :
    models_over_tuple ct_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_new_csp middle_vertex_is_hidden ![0, 0, 0]) = 2 ∧
      models_over_tuple ct_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_new_csp middle_vertex_is_hidden ![0, 0, 2]) = 2 ∧
      models_over_tuple ct_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_new_csp middle_vertex_is_hidden ![1, 0, 0]) = 2 ∧
      models_over_tuple ct_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_new_csp middle_vertex_is_hidden ![1, 0, 1]) = 1 ∧
      models_over_tuple ct_start_new_csp middle_vertex_is_hidden middle_vertex_is_hidden
        (minimal_support_encoding ct_start_new_csp middle_vertex_is_hidden [0, 1, 2])
        (tuple_of_values ct_start_new_csp middle_vertex_is_hidden ![1, 0, 2]) = 2 := by
  simp only [minimal_support_models_over_tuple_eq_selection_count]
  decide +kernel

end counterexamples

end parsimony
