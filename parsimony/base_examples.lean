import parsimony.base_transformation
import parsimony.dropping_blocks

namespace parsimony

theorem single_layer_mdd_unique_extension (diagram : layered_mdd 1)
    (single_root : diagram.node_count 0 = 1) (single_terminal : diagram.node_count 1 = 1)
    (distinct_edges : ∀ layer (first second : Fin (diagram.edge_count layer)),
      diagram.edge_source layer first = diagram.edge_source layer second →
        diagram.edge_label layer first = diagram.edge_label layer second →
          diagram.edge_target layer first = diagram.edge_target layer second → first = second)
    (word : ∀ layer, Fin (diagram.symbol_count layer)) :
    mdd_dtbe_extension_count diagram word ≤ 1 := by
  apply mdd_dtbe_unique_extension diagram _ single_root word
  intro layer first second same_source same_label
  apply distinct_edges layer first second same_source same_label
  have layer_zero : layer = 0 := Subsingleton.elim layer 0
  subst layer_zero
  have terminal_bound : diagram.node_count (Fin.succ 0) = 1 := single_terminal
  have first_lt := (diagram.edge_target 0 first).isLt
  have second_lt := (diagram.edge_target 0 second).isLt
  apply Fin.ext
  omega

theorem one_state_automaton_unique_extension {symbol_count transition_count : ℕ}
    (automaton : finite_automaton 1 symbol_count transition_count)
    (distinct : transitions_are_distinct automaton) {length : ℕ}
    (word : Fin length → Fin symbol_count) :
    nfa_dtbe_extension_count automaton word ≤ 1 := by
  apply deterministic_automaton_unique_extension automaton _ word
  intro first second same_source same_symbol
  exact distinct first second same_source same_symbol (Subsingleton.elim _ _)

theorem empty_word_unique_extension {state_count symbol_count transition_count : ℕ}
    (automaton : finite_automaton state_count symbol_count transition_count)
    (word : Fin 0 → Fin symbol_count) :
    nfa_dtbe_extension_count automaton word ≤ 1 := by
  unfold nfa_dtbe_extension_count
  rw [Fintype.card_le_one_iff]
  rintro ⟨⟨first_nodes, first_edges⟩, first_initial, _⟩
    ⟨⟨second_nodes, second_edges⟩, second_initial, _⟩
  have nodes_eq : first_nodes = second_nodes := by
    funext node
    have node_zero : node = 0 := Fin.ext (by
      have node_lt := node.isLt
      simp only [Fin.val_zero]
      omega)
    rw [node_zero]
    exact first_initial.trans second_initial.symm
  have edges_eq : first_edges = second_edges := funext fun edge => edge.elim0
  subst nodes_eq
  subst edges_eq
  rfl

namespace counterexamples

def two_path_mdd : layered_mdd 2 where
  symbol_count := fun _ => 1
  node_count := fun layer => if layer.val = 1 then 2 else 1
  edge_count := fun _ => 2
  edge_source := fun layer edge => ⟨if layer.val = 1 then edge.val else 0, by
    have edge_lt : edge.val < 2 := edge.isLt
    have same_layer : (Fin.castSucc layer).val = layer.val := Fin.val_castSucc layer
    show (if layer.val = 1 then edge.val else 0) < (if (Fin.castSucc layer).val = 1 then 2 else 1)
    split_ifs <;> omega⟩
  edge_target := fun layer edge => ⟨if layer.val = 0 then edge.val else 0, by
    have edge_lt : edge.val < 2 := edge.isLt
    have next_layer : (Fin.succ layer).val = layer.val + 1 := Fin.val_succ layer
    show (if layer.val = 0 then edge.val else 0) < (if (Fin.succ layer).val = 1 then 2 else 1)
    split_ifs <;> omega⟩
  edge_label := fun _ _ => ⟨0, Nat.zero_lt_one⟩

theorem two_path_mdd_single_root : two_path_mdd.node_count 0 = 1 := by
  decide +kernel

theorem two_path_mdd_single_terminal : two_path_mdd.node_count 2 = 1 := by
  decide +kernel

theorem two_path_mdd_not_deterministic : ¬ is_deterministic_mdd two_path_mdd := by
  unfold is_deterministic_mdd
  decide +kernel

theorem two_path_mdd_two_extensions :
    mdd_dtbe_extension_count two_path_mdd (fun _ => ⟨0, Nat.zero_lt_one⟩) = 2 := by
  decide +kernel

def two_run_automaton : finite_automaton 2 1 2 where
  initial := 0
  accepting := fun _ => true
  transition_source := fun _ => 0
  transition_symbol := fun _ => 0
  transition_target := fun transition => transition

theorem two_run_automaton_distinct : transitions_are_distinct two_run_automaton := by
  unfold transitions_are_distinct
  decide +kernel

theorem two_run_automaton_not_deterministic :
    ¬ is_deterministic_automaton two_run_automaton := by
  unfold is_deterministic_automaton
  decide +kernel

theorem two_run_automaton_two_extensions :
    nfa_dtbe_extension_count two_run_automaton (fun _ : Fin 1 => 0) = 2 := by
  decide +kernel

theorem two_run_automaton_two_state_runs :
    Fintype.card {states : Fin (1 + 1) → Fin 2 //
      is_accepting_state_run two_run_automaton (fun _ : Fin 1 => 0) states} = 2 := by
  rw [← nfa_extension_count_eq_state_run_count two_run_automaton two_run_automaton_distinct]
  exact two_run_automaton_two_extensions

def two_run_dtbe_csp : binary_csp 4 :=
  csp_of_edges 4 [1, 2, 1, 2]
    [(0, 1, [(0, 0), (0, 1)]), (1, 2, [(0, 0), (1, 0)]), (1, 3, [(0, 0), (1, 1)])] (by decide)
    (by decide)

def two_run_tuple : original_tuple two_run_dtbe_csp first_vertex_is_original :=
  fun x => ⟨0, two_run_dtbe_csp.domain_nonempty x.val⟩

theorem two_run_dtbe_order_is_valid : is_tree_order two_run_dtbe_csp [0, 1, 2, 3] := by
  decide +kernel

theorem two_run_dtbe_relation_count :
    relation_count two_run_dtbe_csp first_vertex_is_original = 1 := by
  decide +kernel

theorem two_run_dtbe_extension_count :
    extension_count two_run_dtbe_csp first_vertex_is_original two_run_tuple = 2 := by
  decide +kernel

theorem two_run_dtbe_two_models_per_encoding :
    models_over_tuple two_run_dtbe_csp first_vertex_is_original all_vertices
        (support_encoding two_run_dtbe_csp) two_run_tuple = 2 ∧
      models_over_tuple two_run_dtbe_csp first_vertex_is_original all_vertices
        (direct_encoding two_run_dtbe_csp) two_run_tuple = 2 ∧
      models_over_tuple two_run_dtbe_csp first_vertex_is_original all_vertices
        (min_eo_encoding two_run_dtbe_csp [0, 1, 2, 3]) two_run_tuple = 2 ∧
      log_models_over_tuple two_run_dtbe_csp first_vertex_is_original two_run_tuple = 2 := by
  rw [support_models_over_tuple, direct_models_over_tuple,
    min_eo_models_over_tuple two_run_dtbe_csp first_vertex_is_original [0, 1, 2, 3]
      two_run_dtbe_order_is_valid,
    log_models_over_tuple_eq_extension_count, two_run_dtbe_extension_count]
  exact ⟨rfl, rfl, rfl, rfl⟩

def two_run_reduced_csp : binary_csp 2 :=
  csp_of_edges 2 [1, 1] [(0, 1, [(0, 0)])] (by decide) (by decide)

theorem two_run_reduced_order_is_valid : is_tree_order two_run_reduced_csp [0, 1] := by
  decide +kernel

theorem two_run_reduced_relation_count :
    relation_count two_run_reduced_csp first_vertex_is_original = 1 := by
  decide +kernel

theorem two_run_reduced_has_unique_extension :
    has_unique_extension two_run_reduced_csp first_vertex_is_original := by
  decide +kernel

theorem two_run_reduced_one_model_per_encoding :
    model_count (support_encoding two_run_reduced_csp) = 1 ∧
      model_count (direct_encoding two_run_reduced_csp) = 1 ∧
      model_count (min_eo_encoding two_run_reduced_csp [0, 1]) = 1 ∧
      model_count (partial_support_encoding two_run_reduced_csp first_vertex_is_original) = 1 ∧
      model_count (log_encoding two_run_reduced_csp) = 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rw [log_model_count]
  decide +kernel

end counterexamples

end parsimony
