import Mathlib
import parsimony.definitions

namespace parsimony

variable {vertex_count : ℕ}

def log_valuation_of_assignment (csp : binary_csp vertex_count) (candidate : assignment csp) :
    log_variable csp → Bool :=
  fun bit_variable =>
    value_bit (csp.domain_size bit_variable.1) (candidate bit_variable.1).val bit_variable.2.val

def log_encodes_tuple (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (valuation : log_variable csp → Bool) (tuple : original_tuple csp originals) : Prop :=
  ∀ x : original_vertex originals, ∀ position : Fin (bit_count (csp.domain_size x.val)),
    valuation ⟨x.val, position⟩ = value_bit (csp.domain_size x.val) (tuple x).val position.val

instance (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (valuation : log_variable csp → Bool) (tuple : original_tuple csp originals) :
    Decidable (log_encodes_tuple csp originals valuation tuple) := by
  unfold log_encodes_tuple
  infer_instance

def log_models_over_tuple (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) : ℕ :=
  Fintype.card {valuation : log_variable csp → Bool //
    is_model valuation (log_encoding csp) ∧ log_encodes_tuple csp originals valuation tuple}

def log_is_projection_exact (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) : Prop :=
  (∀ valuation, is_model valuation (log_encoding csp) →
    ∃ tuple, in_relation csp originals tuple ∧ log_encodes_tuple csp originals valuation tuple) ∧
  (∀ tuple, in_relation csp originals tuple →
    ∃ valuation, is_model valuation (log_encoding csp) ∧
      log_encodes_tuple csp originals valuation tuple)

structure composition_problem (original_count part_count : ℕ) : Type 1 where
  domain_size : Fin original_count → ℕ
  block_type : Fin original_count → Type
  block_fintype : ∀ original, Fintype (block_type original)
  block_decidable_eq : ∀ original, DecidableEq (block_type original)
  block_code : ∀ original, Fin (domain_size original) → block_type original → Bool
  block_code_injective : ∀ original, Function.Injective (block_code original)
  scope_type : Fin part_count → Type
  scope_fintype : ∀ part, Fintype (scope_type part)
  scope_decidable_eq : ∀ part, DecidableEq (scope_type part)
  scope_original : ∀ part, scope_type part → Fin original_count
  private_type : Fin part_count → Type
  private_fintype : ∀ part, Fintype (private_type part)
  private_decidable_eq : ∀ part, DecidableEq (private_type part)
  part_formula : ∀ part, cnf_formula
    ((Σ member : scope_type part, block_type (scope_original part member)) ⊕ private_type part)
  part_relation : ∀ part,
    (∀ member : scope_type part, Fin (domain_size (scope_original part member))) → Prop
  part_relation_decidable : ∀ part, DecidablePred (part_relation part)

attribute [instance] composition_problem.block_fintype composition_problem.block_decidable_eq
  composition_problem.scope_fintype composition_problem.scope_decidable_eq
  composition_problem.private_fintype composition_problem.private_decidable_eq
  composition_problem.part_relation_decidable

section composition

variable {original_count part_count : ℕ}

abbrev part_variable (problem : composition_problem original_count part_count)
    (part : Fin part_count) :=
  (Σ member : problem.scope_type part, problem.block_type (problem.scope_original part member)) ⊕
    problem.private_type part

abbrev global_variable (problem : composition_problem original_count part_count) :=
  (Σ original, problem.block_type original) ⊕ (Σ part, problem.private_type part)

def rename_to_global (problem : composition_problem original_count part_count)
    (part : Fin part_count) : part_variable problem part → global_variable problem
  | Sum.inl ⟨member, block_variable⟩ => Sum.inl ⟨problem.scope_original part member, block_variable⟩
  | Sum.inr private_variable => Sum.inr ⟨part, private_variable⟩

def rename_formula {source_type target_type : Type} (rename : source_type → target_type)
    (formula : cnf_formula source_type) : cnf_formula target_type :=
  formula.map fun clause => clause.map fun literal => (rename literal.1, literal.2)

def conjunction_formula (problem : composition_problem original_count part_count) :
    cnf_formula (global_variable problem) :=
  (List.finRange part_count).flatMap fun part =>
    rename_formula (rename_to_global problem part) (problem.part_formula part)

abbrev global_tuple (problem : composition_problem original_count part_count) :=
  ∀ original, Fin (problem.domain_size original)

abbrev part_tuple (problem : composition_problem original_count part_count)
    (part : Fin part_count) :=
  ∀ member : problem.scope_type part, Fin (problem.domain_size (problem.scope_original part member))

def restrict_to_part (problem : composition_problem original_count part_count)
    (tuple : global_tuple problem) (part : Fin part_count) : part_tuple problem part :=
  fun member => tuple (problem.scope_original part member)

def part_encodes (problem : composition_problem original_count part_count) (part : Fin part_count)
    (valuation : part_variable problem part → Bool) (tuple : part_tuple problem part) : Prop :=
  ∀ member block_variable, valuation (Sum.inl ⟨member, block_variable⟩) =
    problem.block_code (problem.scope_original part member) (tuple member) block_variable

instance (problem : composition_problem original_count part_count) (part : Fin part_count)
    (valuation : part_variable problem part → Bool) (tuple : part_tuple problem part) :
    Decidable (part_encodes problem part valuation tuple) := by
  unfold part_encodes
  infer_instance

def part_models_over (problem : composition_problem original_count part_count)
    (part : Fin part_count) (tuple : part_tuple problem part) : ℕ :=
  Fintype.card {valuation : part_variable problem part → Bool //
    is_model valuation (problem.part_formula part) ∧ part_encodes problem part valuation tuple}

def part_is_projection_exact (problem : composition_problem original_count part_count)
    (part : Fin part_count) : Prop :=
  (∀ valuation, is_model valuation (problem.part_formula part) →
    ∃ tuple, problem.part_relation part tuple ∧ part_encodes problem part valuation tuple) ∧
  (∀ tuple, problem.part_relation part tuple →
    ∃ valuation, is_model valuation (problem.part_formula part) ∧
      part_encodes problem part valuation tuple)

def satisfies_all_parts (problem : composition_problem original_count part_count)
    (tuple : global_tuple problem) : Prop :=
  ∀ part, problem.part_relation part (restrict_to_part problem tuple part)

instance (problem : composition_problem original_count part_count) :
    DecidablePred (satisfies_all_parts problem) := fun tuple => by
  unfold satisfies_all_parts
  infer_instance

def global_encodes (problem : composition_problem original_count part_count)
    (valuation : global_variable problem → Bool) (tuple : global_tuple problem) : Prop :=
  ∀ original block_variable, valuation (Sum.inl ⟨original, block_variable⟩) =
    problem.block_code original (tuple original) block_variable

def covers_all_originals (problem : composition_problem original_count part_count) : Prop :=
  ∀ original, ∃ part member, problem.scope_original part member = original

end composition

section selections

variable {vertex_count : ℕ}

def is_selection_over (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool) : Prop :=
  (∀ x (on_x : originals x = true) (a : Fin (csp.domain_size x)),
    selected x a = decide (a = tuple ⟨x, on_x⟩)) ∧
  ∀ x y, csp.adjacent x y = true → earlier_in order x y = true →
    ∀ a : Fin (csp.domain_size x), selected x a = true →
      ∃ b : Fin (csp.domain_size y), csp.allowed x y a b = true ∧ selected y b = true

instance (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)
    (selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool) :
    Decidable (is_selection_over csp originals order tuple selected) := by
  unfold is_selection_over
  infer_instance

def children_compatible_values (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals) (h : Fin vertex_count) :
    Finset (Fin (csp.domain_size h)) :=
  Finset.univ.filter fun b => ∀ c, csp.adjacent h c = true → earlier_in order h c = true →
    ∀ on_c : originals c = true, csp.allowed h c b (tuple ⟨c, on_c⟩) = true

def parent_compatible_values (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)
    (h parent : Fin vertex_count) : Finset (Fin (csp.domain_size h)) :=
  (children_compatible_values csp originals order tuple h).filter fun b =>
    ∀ on_parent : originals parent = true, csp.allowed parent h (tuple ⟨parent, on_parent⟩) b = true

end selections

structure layered_mdd (layer_count : ℕ) where
  symbol_count : Fin layer_count → ℕ
  node_count : Fin (layer_count + 1) → ℕ
  edge_count : Fin layer_count → ℕ
  edge_source : ∀ layer, Fin (edge_count layer) → Fin (node_count layer.castSucc)
  edge_target : ∀ layer, Fin (edge_count layer) → Fin (node_count layer.succ)
  edge_label : ∀ layer, Fin (edge_count layer) → Fin (symbol_count layer)

section base_transformation

variable {layer_count : ℕ}

def is_mdd_dtbe_extension (diagram : layered_mdd layer_count)
    (word : ∀ layer, Fin (diagram.symbol_count layer))
    (node_value : ∀ layer, Fin (diagram.node_count layer))
    (edge_value : ∀ layer, Fin (diagram.edge_count layer)) : Prop :=
  ∀ layer, diagram.edge_label layer (edge_value layer) = word layer ∧
    diagram.edge_source layer (edge_value layer) = node_value layer.castSucc ∧
    diagram.edge_target layer (edge_value layer) = node_value layer.succ

instance (diagram : layered_mdd layer_count) (word : ∀ layer, Fin (diagram.symbol_count layer))
    (node_value : ∀ layer, Fin (diagram.node_count layer))
    (edge_value : ∀ layer, Fin (diagram.edge_count layer)) :
    Decidable (is_mdd_dtbe_extension diagram word node_value edge_value) := by
  unfold is_mdd_dtbe_extension
  infer_instance

def mdd_dtbe_extension_count (diagram : layered_mdd layer_count)
    (word : ∀ layer, Fin (diagram.symbol_count layer)) : ℕ :=
  Fintype.card {values : (∀ layer, Fin (diagram.node_count layer)) ×
      (∀ layer, Fin (diagram.edge_count layer)) //
    is_mdd_dtbe_extension diagram word values.1 values.2}

def is_deterministic_mdd (diagram : layered_mdd layer_count) : Prop :=
  ∀ layer (first second : Fin (diagram.edge_count layer)),
    diagram.edge_source layer first = diagram.edge_source layer second →
      diagram.edge_label layer first = diagram.edge_label layer second → first = second

end base_transformation

structure finite_automaton (state_count symbol_count transition_count : ℕ) where
  initial : Fin state_count
  accepting : Fin state_count → Bool
  transition_source : Fin transition_count → Fin state_count
  transition_symbol : Fin transition_count → Fin symbol_count
  transition_target : Fin transition_count → Fin state_count

section automata

variable {state_count symbol_count transition_count : ℕ}

def is_nfa_dtbe_extension
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (node_value : Fin (length + 1) → Fin state_count)
    (edge_value : Fin length → Fin transition_count) : Prop :=
  node_value 0 = automaton.initial ∧ automaton.accepting (node_value (Fin.last length)) = true ∧
    ∀ layer, automaton.transition_symbol (edge_value layer) = word layer ∧
      automaton.transition_source (edge_value layer) = node_value layer.castSucc ∧
      automaton.transition_target (edge_value layer) = node_value layer.succ

instance (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (node_value : Fin (length + 1) → Fin state_count)
    (edge_value : Fin length → Fin transition_count) :
    Decidable (is_nfa_dtbe_extension automaton word node_value edge_value) := by
  unfold is_nfa_dtbe_extension
  infer_instance

def nfa_dtbe_extension_count
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) : ℕ :=
  Fintype.card {values : (Fin (length + 1) → Fin state_count) × (Fin length → Fin transition_count) //
    is_nfa_dtbe_extension automaton word values.1 values.2}

def is_accepting_transition_run
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (run : Fin length → Fin transition_count) : Prop :=
  (∀ layer, automaton.transition_symbol (run layer) = word layer) ∧
  (∀ (layer : Fin length) (later : Fin length), later.val = layer.val + 1 →
    automaton.transition_target (run layer) = automaton.transition_source (run later)) ∧
  (∀ first : Fin length, first.val = 0 → automaton.transition_source (run first) = automaton.initial) ∧
  (∀ last : Fin length, last.val + 1 = length →
    automaton.accepting (automaton.transition_target (run last)) = true) ∧
  (length = 0 → automaton.accepting automaton.initial = true)

instance (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (run : Fin length → Fin transition_count) :
    Decidable (is_accepting_transition_run automaton word run) := by
  unfold is_accepting_transition_run
  infer_instance

def is_accepting_state_run
    (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (states : Fin (length + 1) → Fin state_count) : Prop :=
  states 0 = automaton.initial ∧ automaton.accepting (states (Fin.last length)) = true ∧
    ∀ layer : Fin length, ∃ transition : Fin transition_count,
      automaton.transition_source transition = states layer.castSucc ∧
      automaton.transition_symbol transition = word layer ∧
      automaton.transition_target transition = states layer.succ

instance (automaton : finite_automaton state_count symbol_count transition_count) {length : ℕ}
    (word : Fin length → Fin symbol_count) (states : Fin (length + 1) → Fin state_count) :
    Decidable (is_accepting_state_run automaton word states) := by
  unfold is_accepting_state_run
  infer_instance

def transitions_are_distinct
    (automaton : finite_automaton state_count symbol_count transition_count) : Prop :=
  ∀ first second : Fin transition_count,
    automaton.transition_source first = automaton.transition_source second →
      automaton.transition_symbol first = automaton.transition_symbol second →
        automaton.transition_target first = automaton.transition_target second → first = second

def is_deterministic_automaton
    (automaton : finite_automaton state_count symbol_count transition_count) : Prop :=
  ∀ first second : Fin transition_count,
    automaton.transition_source first = automaton.transition_source second →
      automaton.transition_symbol first = automaton.transition_symbol second → first = second

end automata

section reduction

variable {vertex_count : ℕ}

abbrev other_vertex (h : Fin vertex_count) := {x : Fin vertex_count // x ≠ h}

abbrev rest_assignment (csp : binary_csp vertex_count) (h : Fin vertex_count) :=
  ∀ x : other_vertex h, Fin (csp.domain_size x.val)

def rest_is_consistent (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (rest : rest_assignment csp h) : Prop :=
  ∀ x y : other_vertex h, csp.adjacent x.val y.val = true →
    csp.allowed x.val y.val (rest x) (rest y) = true

instance (csp : binary_csp vertex_count) (h : Fin vertex_count) (rest : rest_assignment csp h) :
    Decidable (rest_is_consistent csp h rest) := by
  unfold rest_is_consistent
  infer_instance

def rest_encodes_tuple (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (h : Fin vertex_count) (rest : rest_assignment csp h) (tuple : original_tuple csp originals) :
    Prop :=
  ∀ x : other_vertex h, ∀ on_x : originals x.val = true, rest x = tuple ⟨x.val, on_x⟩

instance (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (h : Fin vertex_count) (rest : rest_assignment csp h) (tuple : original_tuple csp originals) :
    Decidable (rest_encodes_tuple csp originals h rest tuple) := by
  unfold rest_encodes_tuple
  infer_instance

abbrev neighbour_vertex (csp : binary_csp vertex_count) (h : Fin vertex_count) :=
  {y : Fin vertex_count // csp.adjacent h y = true}

abbrev neighbour_tuple (csp : binary_csp vertex_count) (h : Fin vertex_count) :=
  ∀ y : neighbour_vertex csp h, Fin (csp.domain_size y.val)

theorem neighbour_ne_center (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (y : neighbour_vertex csp h) : y.val ≠ h := by
  intro y_is_h
  have adjacent_h_y := y.property
  rw [y_is_h, csp.adjacent_irrefl] at adjacent_h_y
  exact absurd adjacent_h_y (by decide)

def neighbour_tuple_of_rest (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (rest : rest_assignment csp h) : neighbour_tuple csp h :=
  fun y => rest ⟨y.val, neighbour_ne_center csp h y⟩

def value_fits_neighbours (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (value : Fin (csp.domain_size h)) (neighbours : neighbour_tuple csp h) : Prop :=
  ∀ y : neighbour_vertex csp h, csp.allowed h y.val value (neighbours y) = true

instance (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (value : Fin (csp.domain_size h)) (neighbours : neighbour_tuple csp h) :
    Decidable (value_fits_neighbours csp h value neighbours) := by
  unfold value_fits_neighbours
  infer_instance

def old_value_count (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (neighbours : neighbour_tuple csp h) : ℕ :=
  Fintype.card {value : Fin (csp.domain_size h) // value_fits_neighbours csp h value neighbours}

abbrev neighbour_box (csp : binary_csp vertex_count) (h : Fin vertex_count) :=
  ∀ y : neighbour_vertex csp h, Finset (Fin (csp.domain_size y.val))

def box_represents (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (box : neighbour_box csp h) (neighbours : neighbour_tuple csp h) : Prop :=
  ∀ y, neighbours y ∈ box y

instance (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (box : neighbour_box csp h) (neighbours : neighbour_tuple csp h) :
    Decidable (box_represents csp h box neighbours) := by
  unfold box_represents
  infer_instance

def box_count (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (table : Finset (neighbour_box csp h)) (neighbours : neighbour_tuple csp h) : ℕ :=
  (table.filter fun box => box_represents csp h box neighbours).card

def is_valid_cc_table (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (table : Finset (neighbour_box csp h)) : Prop :=
  ∀ neighbours : neighbour_tuple csp h,
    (∃ value, value_fits_neighbours csp h value neighbours) ↔
      ∃ box ∈ table, box_represents csp h box neighbours

def eliminated_extension_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (h : Fin vertex_count)
    (tuple : original_tuple csp originals) : ℕ :=
  Fintype.card {rest : rest_assignment csp h // rest_is_consistent csp h rest ∧
    (∃ value, value_fits_neighbours csp h value (neighbour_tuple_of_rest csp h rest)) ∧
    rest_encodes_tuple csp originals h rest tuple}

def reconstructed_extension_count (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (h : Fin vertex_count)
    (table : Finset (neighbour_box csp h)) (tuple : original_tuple csp originals) : ℕ :=
  Fintype.card {pair : rest_assignment csp h × neighbour_box csp h //
    rest_is_consistent csp h pair.1 ∧ pair.2 ∈ table ∧
    box_represents csp h pair.2 (neighbour_tuple_of_rest csp h pair.1) ∧
    rest_encodes_tuple csp originals h pair.1 tuple}

def agree_outside (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (pivot : neighbour_vertex csp h) (first second : neighbour_box csp h) : Prop :=
  ∀ y, y ≠ pivot → first y = second y

instance (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (pivot : neighbour_vertex csp h) (first second : neighbour_box csp h) :
    Decidable (agree_outside csp h pivot first second) := by
  unfold agree_outside
  infer_instance

def merged_box (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (table : Finset (neighbour_box csp h)) (pivot : neighbour_vertex csp h)
    (box : neighbour_box csp h) : neighbour_box csp h :=
  Function.update box pivot
    ((table.filter fun other => agree_outside csp h pivot box other).biUnion fun other => other pivot)

def merge_table (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (table : Finset (neighbour_box csp h)) (pivot : neighbour_vertex csp h) :
    Finset (neighbour_box csp h) :=
  table.image (merged_box csp h table pivot)

def box_of_value (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (value : Fin (csp.domain_size h)) : neighbour_box csp h :=
  fun y => Finset.univ.filter fun b => csp.allowed h y.val value b = true

def value_table (csp : binary_csp vertex_count) (h : Fin vertex_count) :
    Finset (neighbour_box csp h) :=
  Finset.univ.image (box_of_value csp h)

def box_of_tuple (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (neighbours : neighbour_tuple csp h) : neighbour_box csp h :=
  fun y => {neighbours y}

def tuple_table (csp : binary_csp vertex_count) (h : Fin vertex_count) :
    Finset (neighbour_box csp h) :=
  (Finset.univ.filter fun neighbours : neighbour_tuple csp h =>
    ∃ value, value_fits_neighbours csp h value neighbours).image (box_of_tuple csp h)

def merge_along (csp : binary_csp vertex_count) (h : Fin vertex_count)
    (start : Finset (neighbour_box csp h)) (pivots : List (neighbour_vertex csp h)) :
    Finset (neighbour_box csp h) :=
  pivots.foldl (merge_table csp h) start

end reduction

end parsimony
