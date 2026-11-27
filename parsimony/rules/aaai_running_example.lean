import parsimony.bijection
import parsimony.reduction_examples
import parsimony.rules.model_counter

namespace parsimony
namespace rules

open counterexamples

def assignment_of_values {vertex_count : ℕ} (csp : binary_csp vertex_count)
    (values : Fin vertex_count → ℕ) : assignment csp :=
  fun x => ⟨values x % csp.domain_size x, Nat.mod_lt _ (csp.domain_nonempty x)⟩

theorem listed_solutions_are_all {vertex_count solution_count : ℕ} (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (listed : Fin solution_count → assignment csp)
    (listed_solve : ∀ index, is_solution csp (listed index))
    (distinct : Function.Injective fun index => restrict_to_originals csp originals (listed index))
    (counted : Fintype.card {candidate : assignment csp // is_solution csp candidate} = solution_count) :
    has_unique_extension csp originals ∧ relation_count csp originals = solution_count ∧
      ∀ tuple, in_relation csp originals tuple ↔
        ∃ index, restrict_to_originals csp originals (listed index) = tuple := by
  let into : Fin solution_count → {candidate : assignment csp // is_solution csp candidate} :=
    fun index => ⟨listed index, listed_solve index⟩
  have into_injective : Function.Injective into := by
    intro first second same
    apply distinct
    have same_value := congrArg Subtype.val same
    simp only [into] at same_value
    simp only [same_value]
  have into_bijective : Function.Bijective into := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨into_injective, by rw [counted, Fintype.card_fin]⟩
  have every_solution : ∀ candidate, is_solution csp candidate → ∃ index, listed index = candidate := by
    intro candidate solution
    obtain ⟨index, same⟩ := into_bijective.2 ⟨candidate, solution⟩
    exact ⟨index, congrArg Subtype.val same⟩
  have relation_iff : ∀ tuple, in_relation csp originals tuple ↔
      ∃ index, restrict_to_originals csp originals (listed index) = tuple := by
    intro tuple
    constructor
    · rintro ⟨candidate, solution, restricted⟩
      obtain ⟨index, rfl⟩ := every_solution candidate solution
      exact ⟨index, restricted⟩
    · rintro ⟨index, restricted⟩
      exact ⟨listed index, listed_solve index, restricted⟩
  refine ⟨?_, ?_, relation_iff⟩
  · intro tuple relation
    obtain ⟨index, restricted⟩ := (relation_iff tuple).mp relation
    unfold extension_count
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨listed index, listed_solve index, restricted⟩, ?_⟩
    rintro ⟨candidate, solution, candidate_restricted⟩
    obtain ⟨other, rfl⟩ := every_solution candidate solution
    have same := distinct (candidate_restricted.trans restricted.symm)
    simp only [same]
  · unfold relation_count
    have to_tuple : Function.Bijective (fun index : Fin solution_count =>
        (⟨restrict_to_originals csp originals (listed index), (relation_iff _).mpr ⟨index, rfl⟩⟩ :
          {tuple : original_tuple csp originals // in_relation csp originals tuple})) := by
      constructor
      · intro first second same
        exact distinct (congrArg Subtype.val same)
      · rintro ⟨tuple, relation⟩
        obtain ⟨index, restricted⟩ := (relation_iff tuple).mp relation
        exact ⟨index, Subtype.ext restricted⟩
    rw [← Fintype.card_of_bijective to_tuple, Fintype.card_fin]

def raw_csp : binary_csp 13 :=
  csp_of_edges 13 [2, 2, 1, 2, 3, 2, 2, 3, 2, 2, 3, 2, 1]
    [(1, 0, [(0, 0), (1, 1)]),
    (1, 2, [(0, 0), (1, 0)]),
    (1, 3, [(0, 0), (1, 1)]),
    (4, 5, [(0, 1), (1, 0), (2, 0)]),
    (4, 3, [(0, 0), (1, 0), (2, 1)]),
    (4, 6, [(0, 0), (1, 1), (2, 1)]),
    (7, 8, [(0, 0), (1, 0), (2, 1)]),
    (7, 6, [(0, 0), (1, 1), (2, 1)]),
    (7, 9, [(0, 0), (1, 0), (2, 1)]),
    (10, 11, [(0, 0), (1, 1), (2, 0)]),
    (10, 9, [(0, 0), (1, 0), (2, 1)]),
    (10, 12, [(0, 0), (1, 0), (2, 0)])]
    (by decide) (by decide)

def raw_originals : Fin 13 → Bool :=
  fun x => x.val == 0 || x.val == 5 || x.val == 8 || x.val == 11

def raw_listed : Fin 8 → assignment raw_csp :=
  fun index => assignment_of_values raw_csp (
    ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0],
      ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0],
      ![0, 0, 0, 0, 1, 0, 1, 2, 1, 1, 2, 0, 0],
      ![1, 1, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0],
      ![1, 1, 0, 1, 2, 0, 1, 1, 0, 0, 1, 1, 0],
      ![1, 1, 0, 1, 2, 0, 1, 2, 1, 1, 2, 0, 0]] index)

def raw_support_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(0, false), (3, true)], [(3, false), (0, true)]],
    [[(1, false), (4, true)], [(4, false), (1, true)]],
    [[(3, false), (5, false)], [(3, true), (5, true)], [(4, true), (5, false)], [(4, false), (5, true)]],
    [[(6, true)], [(3, false), (6, true)], [(4, false), (6, true)], [(6, false), (3, true), (4, true)]],
    [[(3, false), (7, true)], [(7, false), (3, true)]],
    [[(4, false), (8, true)], [(8, false), (4, true)]],
    [[(7, false), (9, false)], [(7, true), (9, true)], [(8, true), (9, false)], [(8, false), (9, true)]],
    [[(10, false), (7, true)]],
    [[(7, false), (10, true), (11, true)], [(11, false), (7, true)]],
    [[(8, false), (12, true)], [(12, false), (8, true)]],
    [[(10, false), (13, false)], [(10, true), (13, true)], [(11, false), (13, true)]],
    [[(12, true), (14, false)], [(12, false), (14, true)], [(13, true), (14, false)], [(11, true), (14, true), (13, false)], [(11, false), (14, false)]],
    [[(11, false), (15, true)], [(12, false), (15, true)], [(15, false), (11, true), (12, true)]],
    [[(10, false), (16, true)], [(16, false), (10, true)]],
    [[(15, false), (17, false)], [(15, true), (17, true)], [(16, true), (17, false)], [(16, false), (17, true)]],
    [[(10, false), (18, true)], [(18, false), (10, true)]],
    [[(11, false), (19, true)], [(12, false), (19, true)], [(19, false), (11, true), (12, true)]],
    [[(18, false), (20, false)], [(18, true), (20, true)], [(19, true), (20, false)], [(19, false), (20, true)]],
    [[(18, false), (21, true)], [(21, false), (18, true)]],
    [[(22, false), (19, true)]],
    [[(19, false), (22, true), (23, true)], [(23, false), (19, true)]],
    [[(21, false), (24, false)], [(21, true), (24, true)], [(22, false), (24, true)]],
    [[(23, true), (25, false)], [(23, false), (25, true)], [(24, true), (25, false)], [(22, true), (25, true), (24, false)], [(22, false), (25, false)]],
    [[(21, false), (26, true)], [(22, false), (26, true)], [(26, false), (21, true), (22, true)]],
    [[(23, false), (27, true)], [(27, false), (23, true)]],
    [[(26, false), (28, false)], [(26, true), (28, true)], [(27, true), (28, false)], [(27, false), (28, true)]],
    [[(21, false), (29, true)], [(22, false), (29, true)], [(29, false), (21, true), (22, true)]],
    [[(23, false), (30, true)], [(30, false), (23, true)]],
    [[(29, false), (31, false)], [(29, true), (31, true)], [(30, true), (31, false)], [(30, false), (31, true)]],
    [[(32, false), (29, true)]],
    [[(29, false), (32, true), (33, true)], [(33, false), (29, true)]],
    [[(30, false), (34, true)], [(34, false), (30, true)]],
    [[(32, false), (35, false)], [(32, true), (35, true)], [(33, false), (35, true)]],
    [[(34, true), (36, false)], [(34, false), (36, true)], [(35, true), (36, false)], [(33, true), (36, true), (35, false)], [(33, false), (36, false)]],
    [[(32, false), (37, true)], [(34, false), (37, true)], [(37, false), (32, true), (34, true)]],
    [[(33, false), (38, true)], [(38, false), (33, true)]],
    [[(37, false), (39, false)], [(37, true), (39, true)], [(38, true), (39, false)], [(38, false), (39, true)]],
    [[(40, true)], [(32, false), (40, true)], [(33, false), (40, true)], [(34, false), (40, true)], [(40, false), (32, true), (33, true), (34, true)]]]

theorem raw_support_models : model_count (support_encoding raw_csp) = 8 := by
  rw [model_count_eq_level_count _ (variables_in_order raw_csp all_vertices [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]) (by decide +kernel)
    (by decide +kernel) raw_support_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem raw_relation : has_unique_extension raw_csp raw_originals ∧
    relation_count raw_csp raw_originals = 8 ∧
    ∀ tuple, in_relation raw_csp raw_originals tuple ↔
      ∃ index, restrict_to_originals raw_csp raw_originals (raw_listed index) = tuple :=
  listed_solutions_are_all raw_csp raw_originals raw_listed (by decide +kernel) (by decide +kernel)
    (by rw [← support_model_count, raw_support_models])

theorem raw_relation_is_no_two_consecutive_ones :
    ∀ tuple : original_tuple raw_csp raw_originals, in_relation raw_csp raw_originals tuple ↔
      ¬ ((tuple ⟨0, by decide⟩).val = 1 ∧ (tuple ⟨5, by decide⟩).val = 1) ∧
      ¬ ((tuple ⟨5, by decide⟩).val = 1 ∧ (tuple ⟨8, by decide⟩).val = 1) ∧
      ¬ ((tuple ⟨8, by decide⟩).val = 1 ∧ (tuple ⟨11, by decide⟩).val = 1) := by
  intro tuple
  rw [(raw_relation).2.2 tuple]
  revert tuple
  decide +kernel

def raw_root_x1_order : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def raw_root_x1_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(0, false), (3, true)]],
    [[(1, false), (4, true)]],
    [[(3, false), (5, true)], [(4, false), (5, true)]],
    [[(3, false), (6, true)]],
    [[(4, false), (7, true)]],
    [],
    [[(6, false), (8, true), (9, true)]],
    [[(7, false), (10, true)]],
    [[(9, false), (11, true)], [(10, false), (11, true)]],
    [[(8, false), (12, true)]],
    [[(11, false), (13, false)], [(11, true), (13, true)], [(12, true), (13, false)], [(12, false), (13, true)]],
    [[(8, false), (14, true)]],
    [[(9, false), (15, true)], [(10, false), (15, true)]],
    [[(14, false), (16, true)]],
    [],
    [[(15, false), (17, true), (18, true)]],
    [[(16, false), (19, true)], [(17, false), (19, true)]],
    [[(18, false), (20, true)]],
    [[(19, false), (21, false)], [(19, true), (21, true)], [(20, true), (21, false)], [(20, false), (21, true)]],
    [[(16, false), (22, true)], [(17, false), (22, true)]],
    [[(18, false), (23, true)]],
    [],
    [[(22, false), (24, true), (25, true)]],
    [[(23, false), (26, true)]],
    [[(24, false), (27, true)], [(26, false), (27, true)]],
    [[(25, false), (28, true)]],
    [[(27, false), (29, false)], [(27, true), (29, true)], [(28, true), (29, false)], [(28, false), (29, true)]],
    [[(24, false), (30, true)], [(25, false), (30, true)], [(26, false), (30, true)]]]

theorem raw_root_x1_order_is_valid : is_tree_order raw_csp raw_root_x1_order ∧
    root_is_original raw_originals raw_root_x1_order := by
  decide +kernel

theorem raw_root_x1_minimal_support_models :
    model_count (minimal_support_encoding raw_csp raw_originals raw_root_x1_order) = 132 := by
  rw [model_count_eq_level_count _ (variables_in_order raw_csp raw_originals raw_root_x1_order) (by decide +kernel)
    (by decide +kernel) raw_root_x1_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def raw_root_x2_order : List (Fin 13) := [5, 4, 3, 1, 0, 2, 6, 7, 8, 9, 10, 11, 12]

def raw_root_x2_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(1, false), (3, true)]],
    [],
    [[(0, false), (4, true), (5, true)]],
    [[(3, false), (6, true)], [(4, false), (6, true)]],
    [[(5, false), (7, true)]],
    [[(6, false), (8, true)]],
    [[(7, false), (9, true)]],
    [[(8, false), (10, true)]],
    [[(9, false), (11, true)]],
    [[(10, false), (12, false)], [(10, true), (12, true)], [(11, true), (12, false)], [(11, false), (12, true)]],
    [[(8, false), (13, true)], [(9, false), (13, true)]],
    [[(3, false), (14, true)]],
    [[(4, false), (15, true)], [(5, false), (15, true)]],
    [[(14, false), (16, true)]],
    [],
    [[(15, false), (17, true), (18, true)]],
    [[(16, false), (19, true)], [(17, false), (19, true)]],
    [[(18, false), (20, true)]],
    [[(19, false), (21, false)], [(19, true), (21, true)], [(20, true), (21, false)], [(20, false), (21, true)]],
    [[(16, false), (22, true)], [(17, false), (22, true)]],
    [[(18, false), (23, true)]],
    [],
    [[(22, false), (24, true), (25, true)]],
    [[(23, false), (26, true)]],
    [[(24, false), (27, true)], [(26, false), (27, true)]],
    [[(25, false), (28, true)]],
    [[(27, false), (29, false)], [(27, true), (29, true)], [(28, true), (29, false)], [(28, false), (29, true)]],
    [[(24, false), (30, true)], [(25, false), (30, true)], [(26, false), (30, true)]]]

theorem raw_root_x2_order_is_valid : is_tree_order raw_csp raw_root_x2_order ∧
    root_is_original raw_originals raw_root_x2_order := by
  decide +kernel

theorem raw_root_x2_minimal_support_models :
    model_count (minimal_support_encoding raw_csp raw_originals raw_root_x2_order) = 50 := by
  rw [model_count_eq_level_count _ (variables_in_order raw_csp raw_originals raw_root_x2_order) (by decide +kernel)
    (by decide +kernel) raw_root_x2_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def raw_root_x3_order : List (Fin 13) := [8, 7, 6, 4, 3, 1, 0, 2, 5, 9, 10, 11, 12]

def raw_root_x3_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [],
    [[(0, false), (3, true), (4, true)]],
    [[(1, false), (5, true)]],
    [[(3, false), (6, true)]],
    [[(4, false), (7, true)], [(5, false), (7, true)]],
    [[(6, false), (8, true)]],
    [],
    [[(7, false), (9, true), (10, true)]],
    [[(8, false), (11, true)], [(9, false), (11, true)]],
    [[(10, false), (12, true)]],
    [[(11, false), (13, true)]],
    [[(12, false), (14, true)]],
    [[(13, false), (15, true)]],
    [[(14, false), (16, true)]],
    [[(15, false), (17, false)], [(15, true), (17, true)], [(16, true), (17, false)], [(16, false), (17, true)]],
    [[(13, false), (18, true)], [(14, false), (18, true)]],
    [[(9, false), (19, true)], [(10, false), (19, true)]],
    [[(8, false), (20, true)]],
    [[(19, false), (21, false)], [(19, true), (21, true)], [(20, true), (21, false)], [(20, false), (21, true)]],
    [[(3, false), (22, true)], [(4, false), (22, true)]],
    [[(5, false), (23, true)]],
    [],
    [[(22, false), (24, true), (25, true)]],
    [[(23, false), (26, true)]],
    [[(24, false), (27, true)], [(26, false), (27, true)]],
    [[(25, false), (28, true)]],
    [[(27, false), (29, false)], [(27, true), (29, true)], [(28, true), (29, false)], [(28, false), (29, true)]],
    [[(24, false), (30, true)], [(25, false), (30, true)], [(26, false), (30, true)]]]

theorem raw_root_x3_order_is_valid : is_tree_order raw_csp raw_root_x3_order ∧
    root_is_original raw_originals raw_root_x3_order := by
  decide +kernel

theorem raw_root_x3_minimal_support_models :
    model_count (minimal_support_encoding raw_csp raw_originals raw_root_x3_order) = 22 := by
  rw [model_count_eq_level_count _ (variables_in_order raw_csp raw_originals raw_root_x3_order) (by decide +kernel)
    (by decide +kernel) raw_root_x3_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def raw_root_x4_order : List (Fin 13) := [11, 10, 9, 12, 7, 8, 6, 4, 5, 3, 1, 0, 2]

def raw_root_x4_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [],
    [[(1, false), (4, true)]],
    [[(0, false), (3, true), (5, true)]],
    [[(3, false), (6, true)], [(4, false), (6, true)]],
    [[(5, false), (7, true)]],
    [[(3, false), (8, true)], [(4, false), (8, true)], [(5, false), (8, true)]],
    [],
    [[(6, false), (9, true), (10, true)]],
    [[(7, false), (11, true)]],
    [[(9, false), (12, true)], [(10, false), (12, true)]],
    [[(11, false), (13, true)]],
    [[(12, false), (14, false)], [(12, true), (14, true)], [(13, true), (14, false)], [(13, false), (14, true)]],
    [[(9, false), (15, true)]],
    [[(10, false), (16, true)], [(11, false), (16, true)]],
    [[(15, false), (17, true)]],
    [],
    [[(16, false), (18, true), (19, true)]],
    [[(18, false), (20, true)], [(19, false), (20, true)]],
    [[(17, false), (21, true)]],
    [[(20, false), (22, false)], [(20, true), (22, true)], [(21, true), (22, false)], [(21, false), (22, true)]],
    [[(17, false), (23, true)], [(18, false), (23, true)]],
    [[(19, false), (24, true)]],
    [[(23, false), (25, true)]],
    [[(24, false), (26, true)]],
    [[(25, false), (27, true)]],
    [[(26, false), (28, true)]],
    [[(27, false), (29, false)], [(27, true), (29, true)], [(28, true), (29, false)], [(28, false), (29, true)]],
    [[(25, false), (30, true)], [(26, false), (30, true)]]]

theorem raw_root_x4_order_is_valid : is_tree_order raw_csp raw_root_x4_order ∧
    root_is_original raw_originals raw_root_x4_order := by
  decide +kernel

theorem raw_root_x4_minimal_support_models :
    model_count (minimal_support_encoding raw_csp raw_originals raw_root_x4_order) = 14 := by
  rw [model_count_eq_level_count _ (variables_in_order raw_csp raw_originals raw_root_x4_order) (by decide +kernel)
    (by decide +kernel) raw_root_x4_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def compact_csp : binary_csp 6 :=
  csp_of_edges 6 [2, 2, 2, 2, 2, 2]
    [(1, 0, [(0, 0), (1, 0), (1, 1)]),
    (1, 2, [(0, 1), (1, 0)]),
    (1, 3, [(0, 0), (1, 0), (1, 1)]),
    (3, 4, [(0, 0), (1, 1)]),
    (3, 5, [(0, 0), (0, 1), (1, 0)])]
    (by decide) (by decide)

def compact_originals : Fin 6 → Bool :=
  fun x => x.val == 0 || x.val == 2 || x.val == 4 || x.val == 5

def compact_listed : Fin 8 → assignment compact_csp :=
  fun index => assignment_of_values compact_csp (
    ![![0, 0, 1, 0, 0, 0],
      ![0, 0, 1, 0, 0, 1],
      ![0, 1, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 1],
      ![0, 1, 0, 1, 1, 0],
      ![1, 1, 0, 0, 0, 0],
      ![1, 1, 0, 0, 0, 1],
      ![1, 1, 0, 1, 1, 0]] index)

def compact_support_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(3, false), (0, true)]],
    [[(0, false), (3, true), (4, true)], [(1, false), (4, true)], [(4, false), (0, true), (1, true)]],
    [[(3, false), (5, false)], [(3, true), (5, true)], [(4, true), (5, false)], [(4, false), (5, true)]],
    [[(4, false), (6, true)], [(6, false), (4, true)]],
    [[(3, false), (7, true)], [(7, false), (3, true)]],
    [[(6, false), (8, false)], [(6, true), (8, true)], [(7, true), (8, false)], [(7, false), (8, true)]],
    [[(3, false), (9, true)], [(9, false), (3, true), (4, true)]],
    [[(4, false), (9, true), (10, true)], [(10, false), (4, true)]],
    [[(9, false), (11, false)], [(9, true), (11, true)], [(10, true), (11, false)], [(10, false), (11, true)]],
    [[(9, false), (12, true)], [(12, false), (9, true)]],
    [[(10, false), (13, true)], [(13, false), (10, true)]],
    [[(12, false), (14, false)], [(12, true), (14, true)], [(13, true), (14, false)], [(13, false), (14, true)]],
    [[(10, false), (15, true)], [(15, false), (9, true), (10, true)]],
    [[(9, false), (15, true), (16, true)], [(16, false), (9, true)]],
    [[(15, false), (17, false)], [(15, true), (17, true)], [(16, true), (17, false)], [(16, false), (17, true)]]]

theorem compact_support_models : model_count (support_encoding compact_csp) = 8 := by
  rw [model_count_eq_level_count _ (variables_in_order compact_csp all_vertices [0, 1, 2, 3, 4, 5]) (by decide +kernel)
    (by decide +kernel) compact_support_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem compact_relation : has_unique_extension compact_csp compact_originals ∧
    relation_count compact_csp compact_originals = 8 ∧
    ∀ tuple, in_relation compact_csp compact_originals tuple ↔
      ∃ index, restrict_to_originals compact_csp compact_originals (compact_listed index) = tuple :=
  listed_solutions_are_all compact_csp compact_originals compact_listed (by decide +kernel) (by decide +kernel)
    (by rw [← support_model_count, compact_support_models])

theorem compact_relation_is_no_two_consecutive_ones :
    ∀ tuple : original_tuple compact_csp compact_originals, in_relation compact_csp compact_originals tuple ↔
      ¬ ((tuple ⟨0, by decide⟩).val = 1 ∧ (tuple ⟨2, by decide⟩).val = 1) ∧
      ¬ ((tuple ⟨2, by decide⟩).val = 1 ∧ (tuple ⟨4, by decide⟩).val = 1) ∧
      ¬ ((tuple ⟨4, by decide⟩).val = 1 ∧ (tuple ⟨5, by decide⟩).val = 1) := by
  intro tuple
  rw [(compact_relation).2.2 tuple]
  revert tuple
  decide +kernel

def compact_root_x1_order : List (Fin 6) := [0, 1, 2, 3, 4, 5]

def compact_root_x1_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [],
    [[(0, false), (3, true), (4, true)], [(1, false), (4, true)]],
    [[(4, false), (5, true)]],
    [[(3, false), (6, true)]],
    [[(5, false), (7, false)], [(5, true), (7, true)], [(6, true), (7, false)], [(6, false), (7, true)]],
    [[(3, false), (8, true)]],
    [[(4, false), (8, true), (9, true)]],
    [[(8, false), (10, true)]],
    [[(9, false), (11, true)]],
    [[(10, false), (12, false)], [(10, true), (12, true)], [(11, true), (12, false)], [(11, false), (12, true)]],
    [[(9, false), (13, true)]],
    [[(8, false), (13, true), (14, true)]],
    [[(13, false), (15, false)], [(13, true), (15, true)], [(14, true), (15, false)], [(14, false), (15, true)]]]

theorem compact_root_x1_order_is_valid : is_tree_order compact_csp compact_root_x1_order ∧
    root_is_original compact_originals compact_root_x1_order := by
  decide +kernel

theorem compact_root_x1_minimal_support_models :
    model_count (minimal_support_encoding compact_csp compact_originals compact_root_x1_order) = 8 := by
  rw [model_count_eq_level_count _ (variables_in_order compact_csp compact_originals compact_root_x1_order) (by decide +kernel)
    (by decide +kernel) compact_root_x1_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def compact_root_x2_order : List (Fin 6) := [2, 1, 0, 3, 4, 5]

def compact_root_x2_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(1, false), (3, true)]],
    [[(0, false), (4, true)]],
    [[(3, false), (5, true)]],
    [[(4, false), (5, true), (6, true)]],
    [[(5, false), (7, false)], [(5, true), (7, true)], [(6, true), (7, false)], [(6, false), (7, true)]],
    [[(3, false), (8, true)]],
    [[(4, false), (8, true), (9, true)]],
    [[(8, false), (10, true)]],
    [[(9, false), (11, true)]],
    [[(10, false), (12, false)], [(10, true), (12, true)], [(11, true), (12, false)], [(11, false), (12, true)]],
    [[(9, false), (13, true)]],
    [[(8, false), (13, true), (14, true)]],
    [[(13, false), (15, false)], [(13, true), (15, true)], [(14, true), (15, false)], [(14, false), (15, true)]]]

theorem compact_root_x2_order_is_valid : is_tree_order compact_csp compact_root_x2_order ∧
    root_is_original compact_originals compact_root_x2_order := by
  decide +kernel

theorem compact_root_x2_minimal_support_models :
    model_count (minimal_support_encoding compact_csp compact_originals compact_root_x2_order) = 12 := by
  rw [model_count_eq_level_count _ (variables_in_order compact_csp compact_originals compact_root_x2_order) (by decide +kernel)
    (by decide +kernel) compact_root_x2_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def compact_root_x3_order : List (Fin 6) := [4, 3, 1, 0, 2, 5]

def compact_root_x3_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(0, false), (3, true)]],
    [[(1, false), (4, true)]],
    [],
    [[(3, false), (5, true), (6, true)], [(4, false), (6, true)]],
    [[(5, false), (7, true)]],
    [[(6, false), (7, true), (8, true)]],
    [[(7, false), (9, false)], [(7, true), (9, true)], [(8, true), (9, false)], [(8, false), (9, true)]],
    [[(6, false), (10, true)]],
    [[(5, false), (11, true)]],
    [[(10, false), (12, false)], [(10, true), (12, true)], [(11, true), (12, false)], [(11, false), (12, true)]],
    [[(4, false), (13, true)]],
    [[(3, false), (13, true), (14, true)]],
    [[(13, false), (15, false)], [(13, true), (15, true)], [(14, true), (15, false)], [(14, false), (15, true)]]]

theorem compact_root_x3_order_is_valid : is_tree_order compact_csp compact_root_x3_order ∧
    root_is_original compact_originals compact_root_x3_order := by
  decide +kernel

theorem compact_root_x3_minimal_support_models :
    model_count (minimal_support_encoding compact_csp compact_originals compact_root_x3_order) = 12 := by
  rw [model_count_eq_level_count _ (variables_in_order compact_csp compact_originals compact_root_x3_order) (by decide +kernel)
    (by decide +kernel) compact_root_x3_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

def compact_root_x4_order : List (Fin 6) := [5, 3, 1, 4, 0, 2]

def compact_root_x4_levels : List (cnf_formula ℕ) :=
  [[],
    [],
    [[(0, false), (2, false)], [(0, true), (2, true)], [(1, true), (2, false)], [(1, false), (2, true)]],
    [[(1, false), (3, true)]],
    [[(0, false), (3, true), (4, true)]],
    [],
    [[(3, false), (5, true), (6, true)], [(4, false), (6, true)]],
    [[(3, false), (7, true)]],
    [[(4, false), (8, true)]],
    [[(7, false), (9, false)], [(7, true), (9, true)], [(8, true), (9, false)], [(8, false), (9, true)]],
    [[(5, false), (10, true)]],
    [[(6, false), (10, true), (11, true)]],
    [[(10, false), (12, false)], [(10, true), (12, true)], [(11, true), (12, false)], [(11, false), (12, true)]],
    [[(6, false), (13, true)]],
    [[(5, false), (14, true)]],
    [[(13, false), (15, false)], [(13, true), (15, true)], [(14, true), (15, false)], [(14, false), (15, true)]]]

theorem compact_root_x4_order_is_valid : is_tree_order compact_csp compact_root_x4_order ∧
    root_is_original compact_originals compact_root_x4_order := by
  decide +kernel

theorem compact_root_x4_minimal_support_models :
    model_count (minimal_support_encoding compact_csp compact_originals compact_root_x4_order) = 8 := by
  rw [model_count_eq_level_count _ (variables_in_order compact_csp compact_originals compact_root_x4_order) (by decide +kernel)
    (by decide +kernel) compact_root_x4_levels (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end rules
end parsimony
