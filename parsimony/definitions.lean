import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Log

namespace parsimony

structure binary_csp (vertex_count : ℕ) where
  domain_size : Fin vertex_count → ℕ
  domain_nonempty : ∀ x, 0 < domain_size x
  adjacent : Fin vertex_count → Fin vertex_count → Bool
  adjacent_symm : ∀ x y, adjacent x y = adjacent y x
  adjacent_irrefl : ∀ x, adjacent x x = false
  allowed : Fin vertex_count → Fin vertex_count → ℕ → ℕ → Bool
  allowed_symm : ∀ x y, ∀ a : Fin (domain_size x), ∀ b : Fin (domain_size y),
    allowed x y a b = allowed y x b a

variable {vertex_count : ℕ}

def constraint_graph (csp : binary_csp vertex_count) : SimpleGraph (Fin vertex_count) where
  Adj x y := csp.adjacent x y = true
  symm := ⟨fun x y adjacent_x_y => by rw [csp.adjacent_symm y x]; exact adjacent_x_y⟩
  loopless := ⟨fun x adjacent_x_x => by simp [csp.adjacent_irrefl] at adjacent_x_x⟩

def is_binary_constraint_tree (csp : binary_csp vertex_count) : Prop :=
  (constraint_graph csp).IsTree

abbrev assignment (csp : binary_csp vertex_count) :=
  ∀ x : Fin vertex_count, Fin (csp.domain_size x)

def is_solution (csp : binary_csp vertex_count) (candidate : assignment csp) : Prop :=
  ∀ x y, csp.adjacent x y = true → csp.allowed x y (candidate x) (candidate y) = true

instance (csp : binary_csp vertex_count) : DecidablePred (is_solution csp) := fun candidate => by
  unfold is_solution
  infer_instance

abbrev original_vertex (originals : Fin vertex_count → Bool) :=
  {x : Fin vertex_count // originals x = true}

abbrev original_tuple (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool) :=
  ∀ x : original_vertex originals, Fin (csp.domain_size x.val)

def restrict_to_originals (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (candidate : assignment csp) : original_tuple csp originals :=
  fun x => candidate x.val

def in_relation (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) : Prop :=
  ∃ candidate, is_solution csp candidate ∧ restrict_to_originals csp originals candidate = tuple

instance (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool) :
    DecidablePred (in_relation csp originals) := fun tuple => by
  unfold in_relation
  infer_instance

def relation_count (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool) : ℕ :=
  Fintype.card {tuple : original_tuple csp originals // in_relation csp originals tuple}

def extension_count (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) : ℕ :=
  Fintype.card {candidate : assignment csp //
    is_solution csp candidate ∧ restrict_to_originals csp originals candidate = tuple}

def has_unique_extension (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) : Prop :=
  ∀ tuple, in_relation csp originals tuple → extension_count csp originals tuple = 1

instance (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool) :
    Decidable (has_unique_extension csp originals) := by
  unfold has_unique_extension
  infer_instance

def is_tree_order (csp : binary_csp vertex_count) (order : List (Fin vertex_count)) : Prop :=
  order.Nodup ∧ (∀ x, x ∈ order) ∧
    ∀ later : Fin order.length, 0 < later.val →
      (order.take later.val).countP
        (fun earlier_vertex => csp.adjacent earlier_vertex (order.get later)) = 1

instance (csp : binary_csp vertex_count) (order : List (Fin vertex_count)) :
    Decidable (is_tree_order csp order) := by
  unfold is_tree_order
  infer_instance

def root_is_original (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count)) :
    Prop :=
  ∃ root, order.head? = some root ∧ originals root = true

instance (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count)) :
    Decidable (root_is_original originals order) := by
  unfold root_is_original
  infer_instance

def earlier_in (order : List (Fin vertex_count)) (x y : Fin vertex_count) : Bool :=
  decide (order.idxOf x < order.idxOf y)

abbrev cnf_literal (boolean_type : Type) := boolean_type × Bool

abbrev cnf_clause (boolean_type : Type) := List (cnf_literal boolean_type)

abbrev cnf_formula (boolean_type : Type) := List (cnf_clause boolean_type)

def clause_holds {boolean_type : Type} (valuation : boolean_type → Bool)
    (clause : cnf_clause boolean_type) : Prop :=
  ∃ literal ∈ clause, valuation literal.1 = literal.2

instance {boolean_type : Type} [DecidableEq boolean_type] (valuation : boolean_type → Bool)
    (clause : cnf_clause boolean_type) : Decidable (clause_holds valuation clause) := by
  unfold clause_holds
  infer_instance

def is_model {boolean_type : Type} (valuation : boolean_type → Bool)
    (formula : cnf_formula boolean_type) : Prop :=
  ∀ clause ∈ formula, clause_holds valuation clause

instance {boolean_type : Type} [DecidableEq boolean_type] (formula : cnf_formula boolean_type) :
    DecidablePred (fun valuation : boolean_type → Bool => is_model valuation formula) :=
  fun valuation => by
    unfold is_model
    infer_instance

def model_count {boolean_type : Type} [Fintype boolean_type] [DecidableEq boolean_type]
    (formula : cnf_formula boolean_type) : ℕ :=
  Fintype.card {valuation : boolean_type → Bool // is_model valuation formula}

def formula_as_sets {boolean_type : Type} [DecidableEq boolean_type]
    (formula : cnf_formula boolean_type) : Finset (Finset (cnf_literal boolean_type)) :=
  (formula.map List.toFinset).toFinset

abbrev boolean_variable (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool) :=
  (Σ x : Fin vertex_count, Fin (csp.domain_size x)) ⊕
    (Σ x : {x : Fin vertex_count // ladder_on x = true}, Fin (csp.domain_size x.val - 1))

def value_literal (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (x : Fin vertex_count) (a : Fin (csp.domain_size x)) (polarity : Bool) :
    cnf_literal (boolean_variable csp ladder_on) :=
  (Sum.inl ⟨x, a⟩, polarity)

def ladder_literal (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (x : {x : Fin vertex_count // ladder_on x = true}) (i : Fin (csp.domain_size x.val - 1))
    (polarity : Bool) : cnf_literal (boolean_variable csp ladder_on) :=
  (Sum.inr ⟨x, i⟩, polarity)

def exactly_one_clauses {literal_type : Type} :
    (size : ℕ) → (Fin size → Bool → literal_type) → (Fin (size - 1) → Bool → literal_type) →
      List (List literal_type)
  | 0, _, _ => []
  | 1, value_lit, _ => [[value_lit ⟨0, by omega⟩ true]]
  | size + 2, value_lit, ladder_lit =>
    [[value_lit ⟨0, by omega⟩ false, ladder_lit ⟨0, by omega⟩ false],
      [value_lit ⟨0, by omega⟩ true, ladder_lit ⟨0, by omega⟩ true],
      [value_lit ⟨size + 1, by omega⟩ true, ladder_lit ⟨size, by omega⟩ false],
      [value_lit ⟨size + 1, by omega⟩ false, ladder_lit ⟨size, by omega⟩ true]] ++
    (List.finRange size).flatMap fun middle =>
      [[ladder_lit ⟨middle.val, by have := middle.isLt; omega⟩ true,
          ladder_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false],
        [value_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ true,
          ladder_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ true,
          ladder_lit ⟨middle.val, by have := middle.isLt; omega⟩ false],
        [value_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false,
          ladder_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false],
        [value_lit ⟨middle.val + 1, by have := middle.isLt; omega⟩ false,
          ladder_lit ⟨middle.val, by have := middle.isLt; omega⟩ true]]

def exactly_one_part (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool) :
    cnf_formula (boolean_variable csp ladder_on) :=
  (List.finRange vertex_count).flatMap fun x =>
    if on_x : ladder_on x = true then
      exactly_one_clauses (csp.domain_size x) (value_literal csp ladder_on x)
        (ladder_literal csp ladder_on ⟨x, on_x⟩)
    else []

def support_clause (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (x y : Fin vertex_count) (a : Fin (csp.domain_size x)) :
    cnf_clause (boolean_variable csp ladder_on) :=
  value_literal csp ladder_on x a false ::
    ((List.finRange (csp.domain_size y)).filter
        fun b : Fin (csp.domain_size y) => csp.allowed x y a.val b.val).map
      fun b => value_literal csp ladder_on y b true

def clauses_on_chosen_pairs {boolean_type : Type} (chosen : Fin vertex_count → Fin vertex_count → Bool)
    (clauses_of_pair : Fin vertex_count → Fin vertex_count → cnf_formula boolean_type) :
    cnf_formula boolean_type :=
  (List.finRange vertex_count).flatMap fun x =>
    (List.finRange vertex_count).flatMap fun y =>
      if chosen x y then clauses_of_pair x y else []

def support_clauses_of_pair (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool)
    (x y : Fin vertex_count) : cnf_formula (boolean_variable csp ladder_on) :=
  (List.finRange (csp.domain_size x)).map (support_clause csp ladder_on x y)

def all_support_clauses (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool) :
    cnf_formula (boolean_variable csp ladder_on) :=
  clauses_on_chosen_pairs csp.adjacent (support_clauses_of_pair csp ladder_on)

def tree_order_support_clauses (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (order : List (Fin vertex_count)) :
    cnf_formula (boolean_variable csp ladder_on) :=
  clauses_on_chosen_pairs (fun x y => csp.adjacent x y && earlier_in order x y)
    (support_clauses_of_pair csp ladder_on)

def forbidden_clauses_of_pair (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (x y : Fin vertex_count) :
    cnf_formula (boolean_variable csp ladder_on) :=
  (List.finRange (csp.domain_size x)).flatMap fun a =>
    ((List.finRange (csp.domain_size y)).filter
        fun b : Fin (csp.domain_size y) => !csp.allowed x y a.val b.val).map
      fun b => [value_literal csp ladder_on x a false, value_literal csp ladder_on y b false]

def all_forbidden_clauses (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool) :
    cnf_formula (boolean_variable csp ladder_on) :=
  clauses_on_chosen_pairs csp.adjacent (forbidden_clauses_of_pair csp ladder_on)

abbrev all_vertices : Fin vertex_count → Bool := fun _ => true

def support_encoding (csp : binary_csp vertex_count) :
    cnf_formula (boolean_variable csp all_vertices) :=
  exactly_one_part csp all_vertices ++ all_support_clauses csp all_vertices

def partial_support_encoding (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool) :
    cnf_formula (boolean_variable csp originals) :=
  exactly_one_part csp originals ++ all_support_clauses csp originals

def minimal_support_encoding (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) : cnf_formula (boolean_variable csp originals) :=
  exactly_one_part csp originals ++ tree_order_support_clauses csp originals order

def min_eo_encoding (csp : binary_csp vertex_count) (order : List (Fin vertex_count)) :
    cnf_formula (boolean_variable csp all_vertices) :=
  exactly_one_part csp all_vertices ++ tree_order_support_clauses csp all_vertices order

def direct_encoding (csp : binary_csp vertex_count) :
    cnf_formula (boolean_variable csp all_vertices) :=
  exactly_one_part csp all_vertices ++ all_forbidden_clauses csp all_vertices

def bit_count (size : ℕ) : ℕ := Nat.clog 2 size

abbrev log_variable (csp : binary_csp vertex_count) :=
  Σ x : Fin vertex_count, Fin (bit_count (csp.domain_size x))

def value_bit (size value position : ℕ) : Bool :=
  value.testBit (bit_count size - 1 - position)

def range_clauses_of_vertex (csp : binary_csp vertex_count) (x : Fin vertex_count) :
    cnf_formula (log_variable csp) :=
  let last_value := csp.domain_size x - 1
  let positions := List.finRange (bit_count (csp.domain_size x))
  (positions.filter fun position : Fin (bit_count (csp.domain_size x)) =>
      !value_bit (csp.domain_size x) last_value position.val).map
    fun position =>
      (positions.filter fun earlier_position : Fin (bit_count (csp.domain_size x)) =>
          earlier_position < position).map
          (fun earlier_position =>
            ((⟨x, earlier_position⟩ : log_variable csp),
              !value_bit (csp.domain_size x) last_value earlier_position.val)) ++
        [((⟨x, position⟩ : log_variable csp), false)]

def blocking_literals (csp : binary_csp vertex_count) (x : Fin vertex_count)
    (a : Fin (csp.domain_size x)) : cnf_clause (log_variable csp) :=
  (List.finRange (bit_count (csp.domain_size x))).map fun position =>
    ((⟨x, position⟩ : log_variable csp), !value_bit (csp.domain_size x) a.val position.val)

def log_forbidden_clauses_of_pair (csp : binary_csp vertex_count) (x y : Fin vertex_count) :
    cnf_formula (log_variable csp) :=
  (List.finRange (csp.domain_size x)).flatMap fun a =>
    ((List.finRange (csp.domain_size y)).filter
        fun b : Fin (csp.domain_size y) => !csp.allowed x y a.val b.val).map
      fun b => blocking_literals csp x a ++ blocking_literals csp y b

def log_encoding (csp : binary_csp vertex_count) : cnf_formula (log_variable csp) :=
  (List.finRange vertex_count).flatMap (range_clauses_of_vertex csp) ++
    clauses_on_chosen_pairs csp.adjacent (log_forbidden_clauses_of_pair csp)

def encodes_tuple (csp : binary_csp vertex_count) (originals ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (tuple : original_tuple csp originals) :
    Prop :=
  ∀ x : original_vertex originals, ∀ a : Fin (csp.domain_size x.val),
    valuation (Sum.inl ⟨x.val, a⟩) = decide (a = tuple x)

instance (csp : binary_csp vertex_count) (originals ladder_on : Fin vertex_count → Bool)
    (valuation : boolean_variable csp ladder_on → Bool) (tuple : original_tuple csp originals) :
    Decidable (encodes_tuple csp originals ladder_on valuation tuple) := by
  unfold encodes_tuple
  infer_instance

def models_over_tuple (csp : binary_csp vertex_count) (originals ladder_on : Fin vertex_count → Bool)
    (formula : cnf_formula (boolean_variable csp ladder_on))
    (tuple : original_tuple csp originals) : ℕ :=
  Fintype.card {valuation : boolean_variable csp ladder_on → Bool //
    is_model valuation formula ∧ encodes_tuple csp originals ladder_on valuation tuple}

def is_projection_exact (csp : binary_csp vertex_count) (originals ladder_on : Fin vertex_count → Bool)
    (formula : cnf_formula (boolean_variable csp ladder_on)) : Prop :=
  (∀ valuation, is_model valuation formula →
    ∃ tuple, in_relation csp originals tuple ∧ encodes_tuple csp originals ladder_on valuation tuple) ∧
  (∀ tuple, in_relation csp originals tuple →
    ∃ valuation, is_model valuation formula ∧
      encodes_tuple csp originals ladder_on valuation tuple)

def is_parsimonious {boolean_type : Type} [Fintype boolean_type] [DecidableEq boolean_type]
    (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (formula : cnf_formula boolean_type) : Prop :=
  model_count formula = relation_count csp originals

inductive in_upward_set (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (order : List (Fin vertex_count)) (tuple : original_tuple csp originals) :
    ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Prop
  | intro (x : Fin vertex_count) (a : Fin (csp.domain_size x))
      (fits_tuple : ∀ on_x : originals x = true, a = tuple ⟨x, on_x⟩)
      (witness : ∀ y, csp.adjacent x y = true → earlier_in order x y = true →
        Fin (csp.domain_size y))
      (witness_allowed : ∀ y (adjacent_x_y : csp.adjacent x y = true)
        (x_earlier : earlier_in order x y = true),
        csp.allowed x y a (witness y adjacent_x_y x_earlier) = true)
      (witness_in_set : ∀ y (adjacent_x_y : csp.adjacent x y = true)
        (x_earlier : earlier_in order x y = true),
        in_upward_set csp originals order tuple y (witness y adjacent_x_y x_earlier)) :
      in_upward_set csp originals order tuple x a

end parsimony
