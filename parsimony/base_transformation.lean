import parsimony.extended_definitions

namespace parsimony

theorem mdd_dtbe_values_unique {layer_count : ℕ} (diagram : layered_mdd layer_count)
    (deterministic : is_deterministic_mdd diagram) (single_root : diagram.node_count 0 = 1)
    (word : ∀ layer, Fin (diagram.symbol_count layer))
    (first_nodes second_nodes : ∀ layer, Fin (diagram.node_count layer))
    (first_edges second_edges : ∀ layer, Fin (diagram.edge_count layer))
    (first_extension : is_mdd_dtbe_extension diagram word first_nodes first_edges)
    (second_extension : is_mdd_dtbe_extension diagram word second_nodes second_edges) :
    first_nodes = second_nodes ∧ first_edges = second_edges := by
  have nodes_from : ∀ position (bound : position < layer_count + 1),
      first_nodes ⟨position, bound⟩ = second_nodes ⟨position, bound⟩ := by
    intro position
    induction position with
    | zero =>
      intro bound
      have zero_eq : (⟨0, bound⟩ : Fin (layer_count + 1)) = 0 := rfl
      rw [zero_eq]
      have single : Subsingleton (Fin (diagram.node_count 0)) := by
        rw [single_root]
        infer_instance
      exact Subsingleton.elim _ _
    | succ position induction_step =>
      intro bound
      let layer : Fin layer_count := ⟨position, by omega⟩
      have previous : first_nodes layer.castSucc = second_nodes layer.castSucc :=
        induction_step (by omega)
      have source_first := (first_extension layer).2.1
      have source_second := (second_extension layer).2.1
      have same_edge : first_edges layer = second_edges layer := by
        apply deterministic layer
        · rw [source_first, source_second, previous]
        · rw [(first_extension layer).1, (second_extension layer).1]
      have target_first := (first_extension layer).2.2
      have target_second := (second_extension layer).2.2
      show first_nodes layer.succ = second_nodes layer.succ
      rw [← target_first, ← target_second, same_edge]
  have nodes_equal : first_nodes = second_nodes := by
    funext layer
    exact nodes_from layer.val layer.isLt
  refine ⟨nodes_equal, ?_⟩
  funext layer
  apply deterministic layer
  · rw [(first_extension layer).2.1, (second_extension layer).2.1, nodes_equal]
  · rw [(first_extension layer).1, (second_extension layer).1]

theorem mdd_dtbe_unique_extension {layer_count : ℕ} (diagram : layered_mdd layer_count)
    (deterministic : is_deterministic_mdd diagram) (single_root : diagram.node_count 0 = 1)
    (word : ∀ layer, Fin (diagram.symbol_count layer)) :
    mdd_dtbe_extension_count diagram word ≤ 1 := by
  unfold mdd_dtbe_extension_count
  rw [Fintype.card_le_one_iff]
  rintro ⟨⟨first_nodes, first_edges⟩, first_extension⟩
    ⟨⟨second_nodes, second_edges⟩, second_extension⟩
  obtain ⟨nodes_equal, edges_equal⟩ := mdd_dtbe_values_unique diagram deterministic single_root word
    first_nodes second_nodes first_edges second_edges first_extension second_extension
  subst nodes_equal
  subst edges_equal
  rfl

section automata

variable {state_count symbol_count transition_count : ℕ}

def nodes_of_run (automaton : finite_automaton state_count symbol_count transition_count)
    {length : ℕ} (run : Fin length → Fin transition_count) : Fin (length + 1) → Fin state_count :=
  fun position =>
    if bound : position.val < length then automaton.transition_source (run ⟨position.val, bound⟩)
    else if positive : 0 < length then
      automaton.transition_target (run ⟨length - 1, by omega⟩)
    else automaton.initial

theorem nfa_extension_nodes_determined
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (node_value : Fin (length + 1) → Fin state_count)
    (edge_value : Fin length → Fin transition_count)
    (extension : is_nfa_dtbe_extension automaton word node_value edge_value) :
    node_value = nodes_of_run automaton edge_value := by
  obtain ⟨initial_node, _, layers⟩ := extension
  funext position
  unfold nodes_of_run
  by_cases bound : position.val < length
  · rw [dite_eq_left bound]
    have source := (layers ⟨position.val, bound⟩).2.1
    rw [source]
    rfl
  · rw [dite_eq_right bound]
    by_cases positive : 0 < length
    · rw [dite_eq_left positive]
      have target := (layers ⟨length - 1, by omega⟩).2.2
      rw [target]
      congr 1
      ext
      simp only [Fin.val_succ]
      omega
    · rw [dite_eq_right positive]
      have position_zero : position = 0 := by
        ext
        simp only [Fin.val_zero]
        omega
      rw [position_zero]
      exact initial_node

theorem nfa_extension_iff_run
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (run : Fin length → Fin transition_count) :
    is_nfa_dtbe_extension automaton word (nodes_of_run automaton run) run ↔
      is_accepting_transition_run automaton word run := by
  constructor
  · rintro ⟨initial_node, accepting_last, layers⟩
    refine ⟨fun layer => (layers layer).1, ?_, ?_, ?_, ?_⟩
    · intro layer later later_is
      have target := (layers layer).2.2
      rw [target]
      unfold nodes_of_run
      have succ_bound : (layer.succ : Fin (length + 1)).val < length := by
        simp only [Fin.val_succ]
        omega
      rw [dite_eq_left succ_bound]
      congr 2
      ext
      simp only [Fin.val_succ]
      omega
    · intro first first_zero
      have source := (layers first).2.1
      rw [source]
      have castSucc_zero : first.castSucc = 0 := by
        ext
        simp [first_zero]
      rw [castSucc_zero]
      exact initial_node
    · intro last last_is
      have target := (layers last).2.2
      rw [target]
      have succ_last : last.succ = Fin.last length := by
        ext
        simp only [Fin.val_succ, Fin.val_last]
        omega
      rw [succ_last]
      exact accepting_last
    · intro length_zero
      subst length_zero
      have node_zero : nodes_of_run automaton run 0 = automaton.initial := by
        unfold nodes_of_run
        simp
      rw [← node_zero]
      exact accepting_last
  · rintro ⟨symbols, chained, starts, ends, empty_case⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold nodes_of_run
      by_cases positive : 0 < length
      · rw [dite_eq_left (show (0 : Fin (length + 1)).val < length by simpa using positive)]
        exact starts ⟨0, positive⟩ rfl
      · have length_zero : length = 0 := by omega
        subst length_zero
        simp
    · by_cases positive : 0 < length
      · have last_value : nodes_of_run automaton run (Fin.last length) =
            automaton.transition_target (run ⟨length - 1, by omega⟩) := by
          unfold nodes_of_run
          rw [dite_eq_right (by simp), dite_eq_left positive]
        rw [last_value]
        exact ends ⟨length - 1, by omega⟩ (by simp only; omega)
      · have length_zero : length = 0 := by omega
        subst length_zero
        have node_zero : nodes_of_run automaton run (Fin.last 0) = automaton.initial := by
          unfold nodes_of_run
          simp
        rw [node_zero]
        exact empty_case rfl
    · intro layer
      refine ⟨symbols layer, ?_, ?_⟩
      · unfold nodes_of_run
        rw [dite_eq_left (show (layer.castSucc : Fin (length + 1)).val < length by simp)]
        rfl
      · unfold nodes_of_run
        by_cases succ_bound : layer.val + 1 < length
        · rw [dite_eq_left (show (layer.succ : Fin (length + 1)).val < length by
            simpa using succ_bound)]
          exact chained layer ⟨layer.val + 1, succ_bound⟩ rfl
        · rw [dite_eq_right (show ¬ (layer.succ : Fin (length + 1)).val < length by
            simpa using succ_bound), dite_eq_left (show 0 < length by omega)]
          congr 2
          ext
          simp only
          omega

theorem nfa_extension_count_eq_run_count
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) :
    nfa_dtbe_extension_count automaton word =
      Fintype.card {run : Fin length → Fin transition_count //
        is_accepting_transition_run automaton word run} := by
  unfold nfa_dtbe_extension_count
  refine Fintype.card_of_bijective
    (f := fun values => ⟨values.val.2, by
      have nodes_eq := nfa_extension_nodes_determined automaton word values.val.1 values.val.2
        values.property
      have extension := values.property
      rw [nodes_eq] at extension
      exact (nfa_extension_iff_run automaton word values.val.2).mp extension⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨first_nodes, first_edges⟩, first_extension⟩
      ⟨⟨second_nodes, second_edges⟩, second_extension⟩ same
    have edges_equal : first_edges = second_edges := congrArg Subtype.val same
    have first_nodes_eq := nfa_extension_nodes_determined automaton word first_nodes first_edges
      first_extension
    have second_nodes_eq := nfa_extension_nodes_determined automaton word second_nodes second_edges
      second_extension
    subst edges_equal
    apply Subtype.ext
    simp only [Prod.mk.injEq, and_true]
    rw [first_nodes_eq, second_nodes_eq]
  · rintro ⟨run, accepting⟩
    exact ⟨⟨(nodes_of_run automaton run, run),
      (nfa_extension_iff_run automaton word run).mpr accepting⟩, rfl⟩

theorem state_run_of_transition_run
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (run : Fin length → Fin transition_count)
    (accepting : is_accepting_transition_run automaton word run) :
    is_accepting_state_run automaton word (nodes_of_run automaton run) := by
  have extension := (nfa_extension_iff_run automaton word run).mpr accepting
  obtain ⟨initial_node, accepting_last, layers⟩ := extension
  exact ⟨initial_node, accepting_last, fun layer =>
    ⟨run layer, (layers layer).2.1, (layers layer).1, (layers layer).2.2⟩⟩

theorem nfa_extension_count_eq_state_run_count
    (automaton : finite_automaton state_count symbol_count transition_count)
    (distinct : transitions_are_distinct automaton) {length : ℕ}
    (word : Fin length → Fin symbol_count) :
    nfa_dtbe_extension_count automaton word =
      Fintype.card {states : Fin (length + 1) → Fin state_count //
        is_accepting_state_run automaton word states} := by
  rw [nfa_extension_count_eq_run_count]
  refine Fintype.card_of_bijective
    (f := fun run => ⟨nodes_of_run automaton run.val,
      state_run_of_transition_run automaton word run.val run.property⟩) ⟨?_, ?_⟩
  · rintro ⟨first, first_accepting⟩ ⟨second, second_accepting⟩ same
    have nodes_same : nodes_of_run automaton first = nodes_of_run automaton second :=
      congrArg Subtype.val same
    have first_extension := (nfa_extension_iff_run automaton word first).mpr first_accepting
    have second_extension := (nfa_extension_iff_run automaton word second).mpr second_accepting
    apply Subtype.ext
    funext layer
    apply distinct
    · rw [(first_extension.2.2 layer).2.1, (second_extension.2.2 layer).2.1, nodes_same]
    · rw [(first_extension.2.2 layer).1, (second_extension.2.2 layer).1]
    · rw [(first_extension.2.2 layer).2.2, (second_extension.2.2 layer).2.2, nodes_same]
  · rintro ⟨states, accepting_states⟩
    have initial_state := accepting_states.1
    have accepting_last := accepting_states.2.1
    have steps := accepting_states.2.2
    choose run run_source run_symbol run_target using steps
    have extension : is_nfa_dtbe_extension automaton word states run :=
      ⟨initial_state, accepting_last, fun layer =>
        ⟨run_symbol layer, run_source layer, run_target layer⟩⟩
    have nodes_eq := nfa_extension_nodes_determined automaton word states run extension
    refine ⟨⟨run, (nfa_extension_iff_run automaton word run).mp (nodes_eq ▸ extension)⟩, ?_⟩
    apply Subtype.ext
    exact nodes_eq.symm

theorem deterministic_automaton_unique_extension
    (automaton : finite_automaton state_count symbol_count transition_count)
    (deterministic : is_deterministic_automaton automaton) {length : ℕ}
    (word : Fin length → Fin symbol_count) :
    nfa_dtbe_extension_count automaton word ≤ 1 := by
  rw [nfa_extension_count_eq_run_count, Fintype.card_le_one_iff]
  rintro ⟨first, first_accepting⟩ ⟨second, second_accepting⟩
  apply Subtype.ext
  have same_from : ∀ position (bound : position < length),
      first ⟨position, bound⟩ = second ⟨position, bound⟩ := by
    intro position
    induction position with
    | zero =>
      intro bound
      apply deterministic
      · rw [first_accepting.2.2.1 ⟨0, bound⟩ rfl, second_accepting.2.2.1 ⟨0, bound⟩ rfl]
      · rw [first_accepting.1, second_accepting.1]
    | succ position induction_step =>
      intro bound
      have previous := induction_step (by omega)
      apply deterministic
      · rw [← first_accepting.2.1 ⟨position, by omega⟩ ⟨position + 1, bound⟩ rfl,
          ← second_accepting.2.1 ⟨position, by omega⟩ ⟨position + 1, bound⟩ rfl, previous]
      · rw [first_accepting.1, second_accepting.1]
  funext layer
  exact same_from layer.val layer.isLt

end automata

end parsimony
