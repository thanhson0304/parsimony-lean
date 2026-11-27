import parsimony.rules.dtbe

namespace parsimony
namespace rules

open scoped Classical

structure automaton where
  states : Finset ℕ
  symbols : Finset ℕ
  delta : ℕ → ℕ → Finset ℕ
  initial : ℕ
  accepting : Finset ℕ
  initial_mem : initial ∈ states
  accepting_subset : accepting ⊆ states
  delta_closed : ∀ q a p, p ∈ delta q a → q ∈ states ∧ a ∈ symbols ∧ p ∈ states

def code (q a p : ℕ) : ℕ := Nat.pair q (Nat.pair a p)

def code_source (transition : ℕ) : ℕ := (Nat.unpair transition).1

def code_symbol (transition : ℕ) : ℕ := (Nat.unpair (Nat.unpair transition).2).1

def code_target (transition : ℕ) : ℕ := (Nat.unpair (Nat.unpair transition).2).2

theorem code_source_code (q a p : ℕ) : code_source (code q a p) = q := by
  simp [code_source, code]

theorem code_symbol_code (q a p : ℕ) : code_symbol (code q a p) = a := by
  simp [code_symbol, code]

theorem code_target_code (q a p : ℕ) : code_target (code q a p) = p := by
  simp [code_target, code]

theorem code_of_parts (transition : ℕ) :
    code (code_source transition) (code_symbol transition) (code_target transition) = transition := by
  simp [code, code_source, code_symbol, code_target]

noncomputable def transitions (machine : automaton) : Finset ℕ :=
  ((machine.states ×ˢ machine.symbols ×ˢ machine.states).filter fun triple =>
    triple.2.2 ∈ machine.delta triple.1 triple.2.1).image fun triple =>
      code triple.1 triple.2.1 triple.2.2

theorem mem_transitions (machine : automaton) (q a p : ℕ) :
    code q a p ∈ transitions machine ↔ p ∈ machine.delta q a := by
  simp only [transitions, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨other_q, other_a, other_p, ⟨_, member⟩, same⟩
    have same_q := congrArg code_source same
    have same_a := congrArg code_symbol same
    have same_p := congrArg code_target same
    simp only [code_source_code, code_symbol_code, code_target_code] at same_q same_a same_p
    subst same_q same_a same_p
    exact member
  · intro member
    have closed := machine.delta_closed q a p member
    exact ⟨q, a, p, ⟨⟨closed.1, closed.2.1, closed.2.2⟩, member⟩, rfl⟩

noncomputable def nfa_diagram (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) : layered_diagram where
  layer_count := length
  layer_pos := length_pos
  symbols := position_symbols
  nodes := fun layer => if layer = 0 then {machine.initial}
    else if layer = length then machine.accepting else machine.states
  arcs := fun _ => transitions machine
  source := fun _ transition => code_source transition
  label := fun _ transition => code_symbol transition
  target := fun _ transition => code_target transition

def is_accepting_run (machine : automaton) (length : ℕ) (word run : ℕ → ℕ) : Prop :=
  run 0 = machine.initial ∧ (∀ layer < length, run (layer + 1) ∈ machine.delta (run layer) (word layer)) ∧
  run length ∈ machine.accepting ∧ ∀ layer, length < layer → run layer = 0

def accepting_runs (machine : automaton) (length : ℕ) (word : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {run | is_accepting_run machine length word run}

noncomputable def path_of_run (length : ℕ) (word run : ℕ → ℕ) : ℕ → ℕ := fun layer =>
  if layer < length then code (run layer) (word layer) (run (layer + 1)) else 0

noncomputable def run_of_path (length : ℕ) (path : ℕ → ℕ) : ℕ → ℕ := fun layer =>
  if layer < length then code_source (path layer)
  else if layer = length then code_target (path (length - 1)) else 0

theorem path_of_run_at (length : ℕ) (word run : ℕ → ℕ) (layer : ℕ) (layer_lt : layer < length) :
    path_of_run length word run layer = code (run layer) (word layer) (run (layer + 1)) := by
  simp [path_of_run, layer_lt]

theorem path_of_run_spells (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) (tuple run : ℕ → ℕ)
    (in_domains : ∀ layer < length, tuple (original_of layer) ∈ position_symbols layer)
    (accepting : is_accepting_run machine length (fun layer => tuple (original_of layer)) run) :
    path_of_run length (fun layer => tuple (original_of layer)) run ∈
      paths_spelling (nfa_diagram machine length length_pos position_symbols) tuple := by
  obtain ⟨starts, moves, ends, _⟩ := accepting
  refine ⟨⟨fun layer layer_lt => ?_, fun layer inner => ?_, fun layer beyond => ?_⟩,
    fun layer layer_lt => ?_⟩
  · have layer_lt_length : layer < length := layer_lt
    have closed := machine.delta_closed _ _ _ (moves layer layer_lt_length)
    rw [path_of_run_at length _ run layer layer_lt_length]
    simp only [nfa_diagram, code_source_code, code_symbol_code, code_target_code]
    refine ⟨(mem_transitions machine _ _ _).mpr (moves layer layer_lt_length),
      in_domains layer layer_lt_length, ?_, ?_⟩
    · by_cases at_start : layer = 0
      · subst at_start
        simp [starts]
      · have not_end : layer ≠ length := by omega
        simp only [at_start, not_end, ite_false]
        exact closed.1
    · by_cases at_end : layer + 1 = length
      · rw [ite_eq_right (by omega), ite_eq_left at_end, at_end]
        exact ends
      · rw [ite_eq_right (by omega), ite_eq_right at_end]
        exact closed.2.2
  · have first_lt : layer < length := by
      have : layer + 1 < length := inner
      omega
    rw [path_of_run_at length _ run layer first_lt, path_of_run_at length _ run (layer + 1) inner]
    simp only [nfa_diagram, code_source_code, code_target_code]
  · have not_lt : ¬ layer < length := by
      have : length ≤ layer := beyond
      omega
    simp [path_of_run, not_lt]
  · have layer_lt_length : layer < length := layer_lt
    rw [path_of_run_at length _ run layer layer_lt_length]
    simp only [nfa_diagram, code_symbol_code]

theorem run_of_path_accepting (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) (tuple path : ℕ → ℕ)
    (spells : path ∈ paths_spelling (nfa_diagram machine length length_pos position_symbols) tuple) :
    is_accepting_run machine length (fun layer => tuple (original_of layer)) (run_of_path length path) ∧
      path_of_run length (fun layer => tuple (original_of layer)) (run_of_path length path) = path := by
  obtain ⟨⟨arcs, joined, beyond⟩, labels⟩ := spells
  have arcs_at : ∀ layer < length, path layer ∈ transitions machine := fun layer layer_lt =>
    (arcs layer layer_lt).1
  have label_at : ∀ layer < length, code_symbol (path layer) = tuple (original_of layer) :=
    fun layer layer_lt => labels layer layer_lt
  have next_at : ∀ layer < length, run_of_path length path (layer + 1) = code_target (path layer) := by
    intro layer layer_lt
    by_cases inner : layer + 1 < length
    · have stated : code_target (path layer) = code_source (path (layer + 1)) := joined layer inner
      simp only [run_of_path, inner, ite_true]
      exact stated.symm
    · have last : layer + 1 = length := by omega
      have previous : length - 1 = layer := by omega
      unfold run_of_path
      rw [ite_eq_right inner, ite_eq_left last, previous]
  have here_at : ∀ layer < length, run_of_path length path layer = code_source (path layer) := by
    intro layer layer_lt
    simp [run_of_path, layer_lt]
  have moves_at : ∀ layer < length, run_of_path length path (layer + 1) ∈
      machine.delta (run_of_path length path layer) (tuple (original_of layer)) := by
    intro layer layer_lt
    rw [next_at layer layer_lt, here_at layer layer_lt, ← label_at layer layer_lt]
    refine (mem_transitions machine _ _ _).mp ?_
    rw [code_of_parts]
    exact arcs_at layer layer_lt
  refine ⟨⟨?_, moves_at, ?_, fun layer layer_gt => ?_⟩, ?_⟩
  · rw [here_at 0 length_pos]
    have at_root := (arcs 0 length_pos).2.2.1
    simpa [nfa_diagram] using at_root
  · obtain ⟨last, rfl⟩ : ∃ last, length = last + 1 := ⟨length - 1, by omega⟩
    rw [next_at last (by omega)]
    have at_end := (arcs last (by simp [nfa_diagram])).2.2.2
    simpa [nfa_diagram] using at_end
  · have not_lt : ¬ layer < length := by omega
    have not_eq : ¬ layer = length := by omega
    simp [run_of_path, not_lt, not_eq]
  · funext layer
    by_cases layer_lt : layer < length
    · rw [path_of_run_at length _ _ layer layer_lt, next_at layer layer_lt, here_at layer layer_lt,
        ← label_at layer layer_lt]
      exact code_of_parts (path layer)
    · have zero : path layer = 0 := beyond layer (by
        have : length ≤ layer := by omega
        exact this)
      simp [path_of_run, layer_lt, zero]

theorem paths_eq_image_of_runs (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) (tuple : ℕ → ℕ)
    (in_domains : ∀ layer < length, tuple (original_of layer) ∈ position_symbols layer) :
    paths_spelling (nfa_diagram machine length length_pos position_symbols) tuple =
      path_of_run length (fun layer => tuple (original_of layer)) ''
        accepting_runs machine length fun layer => tuple (original_of layer) := by
  ext path
  constructor
  · intro spells
    have both := run_of_path_accepting machine length length_pos position_symbols tuple path spells
    exact ⟨run_of_path length path, both.1, both.2⟩
  · rintro ⟨run, accepting, rfl⟩
    exact path_of_run_spells machine length length_pos position_symbols tuple run in_domains accepting

theorem path_of_run_injective (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (word : ℕ → ℕ) : Set.InjOn (path_of_run length word) (accepting_runs machine length word) := by
  intro first first_mem second second_mem same
  have at_layer : ∀ layer < length, code (first layer) (word layer) (first (layer + 1)) =
      code (second layer) (word layer) (second (layer + 1)) := by
    intro layer layer_lt
    rw [← path_of_run_at length word first layer layer_lt,
      ← path_of_run_at length word second layer layer_lt, same]
  funext layer
  by_cases layer_lt : layer < length
  · have sources := congrArg code_source (at_layer layer layer_lt)
    simpa [code_source_code] using sources
  · by_cases at_end : layer = length
    · subst at_end
      obtain ⟨last, rfl⟩ : ∃ last, layer = last + 1 := ⟨layer - 1, by omega⟩
      have targets := congrArg code_target (at_layer last (by omega))
      simpa [code_target_code] using targets
    · rw [first_mem.2.2.2 layer (by omega), second_mem.2.2.2 layer (by omega)]

theorem nfa_extension_count_eq_run_count (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) (tuple : ℕ → ℕ)
    (in_domains : ∀ layer < length, tuple (original_of layer) ∈ position_symbols layer) :
    extension_count (dtbe (nfa_diagram machine length length_pos position_symbols)) tuple =
      (accepting_runs machine length fun layer => tuple (original_of layer)).ncard := by
  rw [dtbe_extension_count_eq_path_count,
    paths_eq_image_of_runs machine length length_pos position_symbols tuple in_domains]
  exact (path_of_run_injective machine length length_pos _).ncard_image

theorem nfa_relation_in_domains (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) (tuple : ℕ → ℕ)
    (relation : in_relation (dtbe (nfa_diagram machine length length_pos position_symbols)) tuple) :
    ∀ layer < length, tuple (original_of layer) ∈ position_symbols layer := by
  obtain ⟨candidate, solution, agrees⟩ := relation
  intro layer layer_lt
  rw [← agrees _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr layer_lt))]
  exact ((dtbe_solution_iff _ candidate).mp solution).2.1 layer layer_lt

theorem nfa_unique_extension_iff (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (position_symbols : ℕ → Finset ℕ) :
    has_unique_extension (dtbe (nfa_diagram machine length length_pos position_symbols)) ↔
      ∀ word : ℕ → ℕ, (∀ layer < length, word layer ∈ position_symbols layer) →
        (accepting_runs machine length word).ncard ≤ 1 ∧ (accepting_runs machine length word).Finite := by
  constructor
  · intro unique word in_domains
    let tuple : ℕ → ℕ := fun x => word (x / 3)
    have tuple_at : (fun layer => tuple (original_of layer)) = word := by
      funext layer
      have quotient : original_of layer / 3 = layer := by unfold original_of; omega
      simp [tuple, quotient]
    have tuple_domains : ∀ layer < length, tuple (original_of layer) ∈ position_symbols layer := by
      intro layer layer_lt
      rw [congrFun tuple_at layer]
      exact in_domains layer layer_lt
    have counted := nfa_extension_count_eq_run_count machine length length_pos position_symbols tuple
      tuple_domains
    rw [tuple_at] at counted
    have finite : (accepting_runs machine length word).Finite := by
      have image := paths_eq_image_of_runs machine length length_pos position_symbols tuple tuple_domains
      rw [tuple_at] at image
      have whole := extensions_eq_image_of_paths
        (nfa_diagram machine length length_pos position_symbols) tuple
      have extensions_are_finite := extensions_finite
        (dtbe (nfa_diagram machine length length_pos position_symbols)) tuple
      rw [whole, image] at extensions_are_finite
      have inner : Set.InjOn (candidate_of_path (nfa_diagram machine length length_pos position_symbols))
          (path_of_run length word '' accepting_runs machine length word) := by
        rw [← image]
        intro first first_mem second second_mem same
        rw [← path_of_candidate_of_path _ first first_mem.1,
          ← path_of_candidate_of_path _ second second_mem.1, same]
      exact Set.Finite.of_finite_image (Set.Finite.of_finite_image extensions_are_finite inner)
        (path_of_run_injective machine length length_pos word)
    refine ⟨?_, finite⟩
    rw [← counted]
    by_cases relation : in_relation (dtbe (nfa_diagram machine length length_pos position_symbols)) tuple
    · exact (unique tuple relation).le
    · rw [← extension_count_pos_iff] at relation
      omega
  · intro at_most_one tuple relation
    have in_domains := nfa_relation_in_domains machine length length_pos position_symbols tuple relation
    have positive := (extension_count_pos_iff _ tuple).mpr relation
    rw [nfa_extension_count_eq_run_count machine length length_pos position_symbols tuple in_domains]
      at positive ⊢
    have upper := (at_most_one _ in_domains).1
    omega

theorem nfa_unique_extension_iff_at_most_one_run (machine : automaton) (length : ℕ)
    (length_pos : 0 < length) (position_symbols : ℕ → Finset ℕ) :
    has_unique_extension (dtbe (nfa_diagram machine length length_pos position_symbols)) ↔
      ∀ word : ℕ → ℕ, (∀ layer < length, word layer ∈ position_symbols layer) →
        (accepting_runs machine length word).Subsingleton := by
  rw [nfa_unique_extension_iff]
  refine forall_congr' fun word => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨at_most_one, finite⟩ first first_mem second second_mem
    exact (Set.ncard_le_one finite).mp at_most_one first first_mem second second_mem
  · intro subsingleton
    exact ⟨(Set.ncard_le_one subsingleton.finite).mpr fun first first_mem second second_mem =>
      subsingleton first_mem second_mem, subsingleton.finite⟩

theorem deterministic_automaton_unique_extension (machine : automaton) (length : ℕ)
    (length_pos : 0 < length) (position_symbols : ℕ → Finset ℕ)
    (deterministic : ∀ q a, (machine.delta q a).card ≤ 1) :
    has_unique_extension (dtbe (nfa_diagram machine length length_pos position_symbols)) := by
  refine deterministic_dtbe_unique_extension _ ?_ ?_
  · intro layer _ first first_mem second second_mem same_source same_label
    have first_source : code_source first = code_source second := same_source
    have first_label : code_symbol first = code_symbol second := same_label
    have first_in : first ∈ transitions machine := first_mem
    have second_in : second ∈ transitions machine := second_mem
    rw [← code_of_parts first, mem_transitions] at first_in
    rw [← code_of_parts second, mem_transitions, ← first_source, ← first_label] at second_in
    have same_target := Finset.card_le_one.mp (deterministic _ _) _ first_in _ second_in
    rw [← code_of_parts first, ← code_of_parts second, first_source, first_label, same_target]
  · simp [nfa_diagram]

theorem no_run_of_empty_blocks (machine : automaton) (length : ℕ) (length_pos : 0 < length)
    (word : ℕ → ℕ) (empty : machine.accepting = ∅ ∨ transitions machine = ∅) :
    accepting_runs machine length word = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun run accepting => ?_
  rcases empty with no_accepting | no_transition
  · have ends := accepting.2.2.1
    rw [no_accepting] at ends
    exact absurd ends (Finset.notMem_empty _)
  · have moved := (mem_transitions machine _ _ _).mpr (accepting.2.1 0 length_pos)
    rw [no_transition] at moved
    exact absurd moved (Finset.notMem_empty _)

end rules
end parsimony
