import parsimony.minimal_support_counting
import parsimony.counterexamples

namespace parsimony

variable {vertex_count : ℕ}

def masked_restriction {boolean_type : Type} [DecidableEq boolean_type]
    (kept : Finset boolean_type) (valuation : boolean_type → Bool) : boolean_type → Bool :=
  fun variable_name => if variable_name ∈ kept then valuation variable_name else false

def projected_models {boolean_type : Type} [DecidableEq boolean_type] [Fintype boolean_type]
    (models : Finset (boolean_type → Bool)) (kept : Finset boolean_type) :
    Finset (boolean_type → Bool) :=
  models.image (masked_restriction kept)

def model_set {boolean_type : Type} [DecidableEq boolean_type] [Fintype boolean_type]
    (formula : cnf_formula boolean_type) : Finset (boolean_type → Bool) :=
  Finset.univ.filter fun valuation => is_model valuation formula

def projected_count {boolean_type : Type} [DecidableEq boolean_type] [Fintype boolean_type]
    (formula : cnf_formula boolean_type) (kept : Finset boolean_type) : ℕ :=
  (projected_models (model_set formula) kept).card

theorem masked_restriction_eq_iff {boolean_type : Type} [DecidableEq boolean_type]
    (kept : Finset boolean_type) (first second : boolean_type → Bool) :
    masked_restriction kept first = masked_restriction kept second ↔
      ∀ variable_name ∈ kept, first variable_name = second variable_name := by
  constructor
  · intro same variable_name kept_variable
    have at_variable := congrFun same variable_name
    simpa [masked_restriction, kept_variable] using at_variable
  · intro agree
    funext variable_name
    by_cases kept_variable : variable_name ∈ kept
    · simp [masked_restriction, kept_variable, agree variable_name kept_variable]
    · simp [masked_restriction, kept_variable]

theorem masked_restriction_of_subset {boolean_type : Type} [DecidableEq boolean_type]
    (small large : Finset boolean_type) (small_subset : small ⊆ large)
    (valuation : boolean_type → Bool) :
    masked_restriction small (masked_restriction large valuation) =
      masked_restriction small valuation := by
  funext variable_name
  by_cases small_variable : variable_name ∈ small
  · simp [masked_restriction, small_variable, small_subset small_variable]
  · simp [masked_restriction, small_variable]

theorem masked_restriction_univ {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (valuation : boolean_type → Bool) :
    masked_restriction Finset.univ valuation = valuation := by
  funext variable_name
  simp [masked_restriction]

theorem projected_models_of_subset {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (models : Finset (boolean_type → Bool))
    (small large : Finset boolean_type) (small_subset : small ⊆ large) :
    projected_models models small =
      (projected_models models large).image (masked_restriction small) := by
  unfold projected_models
  rw [Finset.image_image]
  congr 1
  funext valuation
  exact (masked_restriction_of_subset small large small_subset valuation).symm

theorem projected_card_le_of_subset {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (models : Finset (boolean_type → Bool))
    (small large : Finset boolean_type) (small_subset : small ⊆ large) :
    (projected_models models small).card ≤ (projected_models models large).card := by
  rw [projected_models_of_subset models small large small_subset]
  exact Finset.card_image_le

theorem projected_card_eq_iff {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (models : Finset (boolean_type → Bool))
    (small large : Finset boolean_type) (small_subset : small ⊆ large) :
    (projected_models models small).card = (projected_models models large).card ↔
      ∀ first ∈ models, ∀ second ∈ models,
        (∀ variable_name ∈ small, first variable_name = second variable_name) →
          ∀ variable_name ∈ large, first variable_name = second variable_name := by
  rw [projected_models_of_subset models small large small_subset, Finset.card_image_iff]
  constructor
  · intro injective first first_model second second_model agree_small
    have first_mem : masked_restriction large first ∈ projected_models models large :=
      Finset.mem_image_of_mem (masked_restriction large) first_model
    have second_mem : masked_restriction large second ∈ projected_models models large :=
      Finset.mem_image_of_mem (masked_restriction large) second_model
    have same_small : masked_restriction small (masked_restriction large first) =
        masked_restriction small (masked_restriction large second) := by
      rw [masked_restriction_of_subset small large small_subset,
        masked_restriction_of_subset small large small_subset]
      exact (masked_restriction_eq_iff small first second).mpr agree_small
    exact (masked_restriction_eq_iff large first second).mp
      (injective (Finset.mem_coe.mpr first_mem) (Finset.mem_coe.mpr second_mem) same_small)
  · intro agree first_projected first_mem second_projected second_mem same_small
    obtain ⟨first, first_model, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp first_mem)
    obtain ⟨second, second_model, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp second_mem)
    rw [masked_restriction_of_subset small large small_subset,
      masked_restriction_of_subset small large small_subset] at same_small
    exact (masked_restriction_eq_iff large first second).mpr
      (agree first first_model second second_model
        ((masked_restriction_eq_iff small first second).mp same_small))

theorem drop_keeps_count_iff {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (models : Finset (boolean_type → Bool))
    (kept dropped : Finset boolean_type) (dropped_subset : dropped ⊆ kept) :
    (projected_models models (kept \ dropped)).card = (projected_models models kept).card ↔
      ∀ first ∈ projected_models models kept, ∀ second ∈ projected_models models kept,
        (∀ variable_name ∈ kept \ dropped, first variable_name = second variable_name) →
          ∀ variable_name ∈ dropped, first variable_name = second variable_name := by
  rw [projected_card_eq_iff models (kept \ dropped) kept Finset.sdiff_subset]
  constructor
  · intro agree first first_mem second second_mem agree_rest variable_name dropped_variable
    obtain ⟨first_model, first_in, rfl⟩ := Finset.mem_image.mp first_mem
    obtain ⟨second_model, second_in, rfl⟩ := Finset.mem_image.mp second_mem
    have kept_variable := dropped_subset dropped_variable
    have rest_agree : ∀ other ∈ kept \ dropped, first_model other = second_model other := by
      intro other other_rest
      have at_other := agree_rest other other_rest
      have other_kept := (Finset.mem_sdiff.mp other_rest).1
      simpa [masked_restriction, other_kept] using at_other
    have full_agree := agree first_model first_in second_model second_in rest_agree
      variable_name kept_variable
    simp [masked_restriction, kept_variable, full_agree]
  · intro patterns first first_in second second_in agree_rest variable_name kept_variable
    by_cases dropped_variable : variable_name ∈ dropped
    · have first_mem : masked_restriction kept first ∈ projected_models models kept :=
        Finset.mem_image_of_mem (masked_restriction kept) first_in
      have second_mem : masked_restriction kept second ∈ projected_models models kept :=
        Finset.mem_image_of_mem (masked_restriction kept) second_in
      have masked_rest : ∀ other ∈ kept \ dropped,
          masked_restriction kept first other = masked_restriction kept second other := by
        intro other other_rest
        have other_kept := (Finset.mem_sdiff.mp other_rest).1
        simp [masked_restriction, other_kept, agree_rest other other_rest]
      have at_variable := patterns _ first_mem _ second_mem masked_rest variable_name
        dropped_variable
      simpa [masked_restriction, kept_variable] using at_variable
    · exact agree_rest variable_name (Finset.mem_sdiff.mpr ⟨kept_variable, dropped_variable⟩)

theorem drop_keeps_count_iff_unique_pattern {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (models : Finset (boolean_type → Bool))
    (kept dropped : Finset boolean_type) :
    (projected_models models (kept \ dropped)).card = (projected_models models kept).card ↔
      ∀ rest ∈ projected_models models (kept \ dropped),
        ∃! full, full ∈ projected_models models kept ∧
          masked_restriction (kept \ dropped) full = rest := by
  rw [projected_models_of_subset models (kept \ dropped) kept Finset.sdiff_subset,
    Finset.card_image_iff]
  constructor
  · intro injective rest rest_mem
    obtain ⟨full, full_mem, full_maps⟩ := Finset.mem_image.mp rest_mem
    refine ⟨full, ⟨full_mem, full_maps⟩, ?_⟩
    rintro other ⟨other_mem, other_maps⟩
    exact injective (Finset.mem_coe.mpr other_mem) (Finset.mem_coe.mpr full_mem)
      (other_maps.trans full_maps.symm)
  · intro unique first first_mem second second_mem same_rest
    have rest_mem : masked_restriction (kept \ dropped) first ∈
        (projected_models models kept).image (masked_restriction (kept \ dropped)) :=
      Finset.mem_image_of_mem _ (Finset.mem_coe.mp first_mem)
    exact (unique _ rest_mem).unique ⟨Finset.mem_coe.mp first_mem, rfl⟩
      ⟨Finset.mem_coe.mp second_mem, same_rest.symm⟩

theorem model_count_eq_model_set_card {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (formula : cnf_formula boolean_type) :
    model_count formula = (model_set formula).card := by
  unfold model_count model_set
  exact Fintype.card_subtype _

theorem projected_count_univ {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (formula : cnf_formula boolean_type) :
    projected_count formula Finset.univ = model_count formula := by
  unfold projected_count projected_models
  rw [model_count_eq_model_set_card]
  have identity : masked_restriction (Finset.univ : Finset boolean_type) = id :=
    funext fun valuation => masked_restriction_univ valuation
  rw [identity, Finset.image_id]

def owned_variables {boolean_type : Type} [Fintype boolean_type]
    (owner : boolean_type → Fin vertex_count) (vertices : Finset (Fin vertex_count)) :
    Finset boolean_type :=
  Finset.univ.filter fun variable_name => owner variable_name ∈ vertices

def original_vertices (originals : Fin vertex_count → Bool) : Finset (Fin vertex_count) :=
  Finset.univ.filter fun x => originals x = true

def block_owner (csp : binary_csp vertex_count) (ladder_on : Fin vertex_count → Bool) :
    boolean_variable csp ladder_on → Fin vertex_count
  | Sum.inl pair => pair.1
  | Sum.inr pair => pair.1.val

def bit_owner (csp : binary_csp vertex_count) : log_variable csp → Fin vertex_count :=
  fun bit_variable => bit_variable.1

def is_original_coding {boolean_type : Type} (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (owner : boolean_type → Fin vertex_count)
    (formula : cnf_formula boolean_type)
    (encodes : (boolean_type → Bool) → original_tuple csp originals → Prop) : Prop :=
  (∀ valuation, is_model valuation formula →
    ∃ tuple, in_relation csp originals tuple ∧ encodes valuation tuple) ∧
  (∀ tuple, in_relation csp originals tuple →
    ∃ valuation, is_model valuation formula ∧ encodes valuation tuple) ∧
  (∀ first second tuple, is_model first formula → encodes first tuple →
    is_model second formula → encodes second tuple →
    ∀ variable_name, originals (owner variable_name) = true →
      first variable_name = second variable_name) ∧
  (∀ first second first_tuple second_tuple, encodes first first_tuple →
    encodes second second_tuple →
    (∀ variable_name, originals (owner variable_name) = true →
      first variable_name = second variable_name) →
    first_tuple = second_tuple)

def block_fixed_by_tuple {boolean_type : Type} (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (owner : boolean_type → Fin vertex_count)
    (formula : cnf_formula boolean_type)
    (encodes : (boolean_type → Bool) → original_tuple csp originals → Prop)
    (tuple : original_tuple csp originals) (h : Fin vertex_count) : Prop :=
  ∀ first second, is_model first formula → encodes first tuple →
    is_model second formula → encodes second tuple →
    ∀ variable_name, owner variable_name = h → first variable_name = second variable_name

def extensions_agree_on (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) (h : Fin vertex_count) : Prop :=
  ∀ first second : assignment csp, is_solution csp first →
    restrict_to_originals csp originals first = tuple → is_solution csp second →
    restrict_to_originals csp originals second = tuple → first h = second h

theorem original_projected_count {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (owner : boolean_type → Fin vertex_count) (formula : cnf_formula boolean_type)
    (encodes : (boolean_type → Bool) → original_tuple csp originals → Prop)
    (coding : is_original_coding csp originals owner formula encodes) :
    projected_count formula (owned_variables owner (original_vertices originals)) =
      relation_count csp originals := by
  obtain ⟨model_tuple, tuple_model, same_tuple_agree, agree_same_tuple⟩ := coding
  have owned_iff : ∀ variable_name,
      variable_name ∈ owned_variables owner (original_vertices originals) ↔
        originals (owner variable_name) = true := by
    intro variable_name
    simp [owned_variables, original_vertices]
  unfold projected_count projected_models model_set relation_count
  rw [Fintype.card_subtype]
  symm
  refine Finset.card_bij
    (fun tuple tuple_mem => masked_restriction (owned_variables owner (original_vertices originals))
      (Classical.choose (tuple_model tuple (Finset.mem_filter.mp tuple_mem).2))) ?_ ?_ ?_
  · intro tuple tuple_mem
    have chosen_spec :=
      Classical.choose_spec (tuple_model tuple (Finset.mem_filter.mp tuple_mem).2)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, chosen_spec.1⟩)
  · intro first first_mem second second_mem same_pattern
    have first_spec :=
      Classical.choose_spec (tuple_model first (Finset.mem_filter.mp first_mem).2)
    have second_spec :=
      Classical.choose_spec (tuple_model second (Finset.mem_filter.mp second_mem).2)
    refine agree_same_tuple _ _ first second first_spec.2 second_spec.2 ?_
    intro variable_name original_owner
    exact (masked_restriction_eq_iff _ _ _).mp same_pattern variable_name
      ((owned_iff variable_name).mpr original_owner)
  · intro pattern pattern_mem
    obtain ⟨valuation, valuation_mem, rfl⟩ := Finset.mem_image.mp pattern_mem
    have model := (Finset.mem_filter.mp valuation_mem).2
    obtain ⟨tuple, in_rel, encoded⟩ := model_tuple valuation model
    refine ⟨tuple, Finset.mem_filter.mpr ⟨Finset.mem_univ _, in_rel⟩, ?_⟩
    have chosen_spec := Classical.choose_spec (tuple_model tuple in_rel)
    apply (masked_restriction_eq_iff _ _ _).mpr
    intro variable_name owned
    exact same_tuple_agree _ _ tuple chosen_spec.1 chosen_spec.2 model encoded variable_name
      ((owned_iff variable_name).mp owned)

theorem keep_blocks_iff {boolean_type : Type} [DecidableEq boolean_type] [Fintype boolean_type]
    (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (owner : boolean_type → Fin vertex_count) (formula : cnf_formula boolean_type)
    (encodes : (boolean_type → Bool) → original_tuple csp originals → Prop)
    (coding : is_original_coding csp originals owner formula encodes)
    (kept_hidden : Finset (Fin vertex_count)) :
    projected_count formula (owned_variables owner (original_vertices originals ∪ kept_hidden)) =
        relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        block_fixed_by_tuple csp originals owner formula encodes tuple h := by
  rw [← original_projected_count csp originals owner formula encodes coding]
  have subset : owned_variables owner (original_vertices originals) ⊆
      owned_variables owner (original_vertices originals ∪ kept_hidden) := by
    intro variable_name owned
    simp only [owned_variables, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at owned ⊢
    exact Or.inl owned
  unfold projected_count
  refine (eq_comm.trans (projected_card_eq_iff (model_set formula) _ _ subset)).trans ?_
  obtain ⟨model_tuple, _, same_tuple_agree, agree_same_tuple⟩ := coding
  have original_owned : ∀ variable_name,
      variable_name ∈ owned_variables owner (original_vertices originals) ↔
        originals (owner variable_name) = true := by
    intro variable_name
    simp [owned_variables, original_vertices]
  constructor
  · intro agree tuple _ h h_kept first second first_model first_encodes second_model
      second_encodes variable_name owner_is
    have first_mem : first ∈ model_set formula :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, first_model⟩
    have second_mem : second ∈ model_set formula :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, second_model⟩
    apply agree first first_mem second second_mem
    · intro other other_owned
      exact same_tuple_agree first second tuple first_model first_encodes second_model
        second_encodes other ((original_owned other).mp other_owned)
    · simp [owned_variables, owner_is, h_kept]
  · intro fixed first first_mem second second_mem agree_originals variable_name owned
    have first_model := (Finset.mem_filter.mp first_mem).2
    have second_model := (Finset.mem_filter.mp second_mem).2
    obtain ⟨first_tuple, first_in_rel, first_encodes⟩ := model_tuple first first_model
    obtain ⟨second_tuple, _, second_encodes⟩ := model_tuple second second_model
    have same_tuple : first_tuple = second_tuple :=
      agree_same_tuple first second first_tuple second_tuple first_encodes second_encodes
        fun other original_owner =>
          agree_originals other ((original_owned other).mpr original_owner)
    rw [← same_tuple] at second_encodes
    have owner_mem : owner variable_name ∈ original_vertices originals ∪ kept_hidden := by
      simpa [owned_variables] using owned
    rcases Finset.mem_union.mp owner_mem with original_owner | hidden_owner
    · exact agree_originals variable_name (by simpa [owned_variables] using original_owner)
    · exact fixed first_tuple first_in_rel (owner variable_name) hidden_owner first second
        first_model first_encodes second_model second_encodes variable_name rfl

theorem encodes_tuple_agree_unique (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (first second : boolean_variable csp ladder_on → Bool)
    (first_tuple second_tuple : original_tuple csp originals)
    (first_encodes : encodes_tuple csp originals ladder_on first first_tuple)
    (second_encodes : encodes_tuple csp originals ladder_on second second_tuple)
    (agree : ∀ variable_name, originals (block_owner csp ladder_on variable_name) = true →
      first variable_name = second variable_name) :
    first_tuple = second_tuple := by
  funext x
  have at_value := (agree (Sum.inl ⟨x.val, first_tuple x⟩) x.property).symm
  rw [first_encodes x (first_tuple x), second_encodes x (first_tuple x)] at at_value
  simpa using at_value

theorem exactly_one_models_agree_on_originals (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (first second : boolean_variable csp ladder_on → Bool) (tuple : original_tuple csp originals)
    (first_blocks : is_model first (exactly_one_part csp ladder_on))
    (second_blocks : is_model second (exactly_one_part csp ladder_on))
    (first_encodes : encodes_tuple csp originals ladder_on first tuple)
    (second_encodes : encodes_tuple csp originals ladder_on second tuple) :
    ∀ variable_name, originals (block_owner csp ladder_on variable_name) = true →
      first variable_name = second variable_name := by
  have chosen_is : ∀ valuation : boolean_variable csp ladder_on → Bool,
      encodes_tuple csp originals ladder_on valuation tuple →
      ∀ x (on_x : ladder_on x = true) (original_x : originals x = true) chosen,
        block_is_fixed csp ladder_on valuation x on_x chosen →
          tuple ⟨x, original_x⟩ = chosen := by
    intro valuation encodes x on_x original_x chosen fixed
    have at_value := (fixed.1 (tuple ⟨x, original_x⟩)).symm
    rw [encodes ⟨x, original_x⟩ (tuple ⟨x, original_x⟩)] at at_value
    simpa using at_value
  rintro (⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩) original_owner
  · change originals x = true at original_owner
    rw [first_encodes ⟨x, original_owner⟩ a, second_encodes ⟨x, original_owner⟩ a]
  · change originals x = true at original_owner
    obtain ⟨first_chosen, first_fixed⟩ :=
      (is_model_exactly_one_part_iff csp ladder_on first).mp first_blocks x on_x
    obtain ⟨second_chosen, second_fixed⟩ :=
      (is_model_exactly_one_part_iff csp ladder_on second).mp second_blocks x on_x
    rw [first_fixed.2 i, second_fixed.2 i,
      ← chosen_is first first_encodes x on_x original_owner first_chosen first_fixed,
      ← chosen_is second second_encodes x on_x original_owner second_chosen second_fixed]

theorem original_coding_of_projection_exact (csp : binary_csp vertex_count)
    (originals ladder_on : Fin vertex_count → Bool)
    (rest : cnf_formula (boolean_variable csp ladder_on))
    (projection_exact : is_projection_exact csp originals ladder_on
      (exactly_one_part csp ladder_on ++ rest)) :
    is_original_coding csp originals (block_owner csp ladder_on)
      (exactly_one_part csp ladder_on ++ rest) (encodes_tuple csp originals ladder_on) := by
  refine ⟨projection_exact.1, projection_exact.2, ?_, ?_⟩
  · intro first second tuple first_model first_encodes second_model second_encodes
    exact exactly_one_models_agree_on_originals csp originals ladder_on first second tuple
      ((is_model_append first _ _).mp first_model).1
      ((is_model_append second _ _).mp second_model).1 first_encodes second_encodes
  · intro first second first_tuple second_tuple first_encodes second_encodes agree
    exact encodes_tuple_agree_unique csp originals ladder_on first second first_tuple
      second_tuple first_encodes second_encodes agree

theorem support_original_coding (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_original_coding csp originals (block_owner csp all_vertices) (support_encoding csp)
      (encodes_tuple csp originals all_vertices) :=
  original_coding_of_projection_exact csp originals all_vertices
    (all_support_clauses csp all_vertices) (support_is_projection_exact csp originals)

theorem direct_original_coding (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) :
    is_original_coding csp originals (block_owner csp all_vertices) (direct_encoding csp)
      (encodes_tuple csp originals all_vertices) :=
  original_coding_of_projection_exact csp originals all_vertices
    (all_forbidden_clauses csp all_vertices) (direct_is_projection_exact csp originals)

theorem min_eo_original_coding (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) :
    is_original_coding csp originals (block_owner csp all_vertices) (min_eo_encoding csp order)
      (encodes_tuple csp originals all_vertices) :=
  original_coding_of_projection_exact csp originals all_vertices
    (tree_order_support_clauses csp all_vertices order)
    (min_eo_is_projection_exact csp originals order tree_order)

theorem partial_support_original_coding (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) :
    is_original_coding csp originals (block_owner csp originals)
      (partial_support_encoding csp originals) (encodes_tuple csp originals originals) :=
  original_coding_of_projection_exact csp originals originals
    (all_support_clauses csp originals)
    (partial_support_is_projection_exact csp originals tree has_original)

theorem minimal_support_original_coding (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order) :
    is_original_coding csp originals (block_owner csp originals)
      (minimal_support_encoding csp originals order) (encodes_tuple csp originals originals) :=
  original_coding_of_projection_exact csp originals originals
    (tree_order_support_clauses csp originals order)
    (minimal_support_is_projection_exact csp originals order tree_order root_original)

theorem log_original_coding (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool) :
    is_original_coding csp originals (bit_owner csp) (log_encoding csp)
      (log_encodes_tuple csp originals) := by
  obtain ⟨model_tuple, tuple_model⟩ := log_is_projection_exact_theorem csp originals
  refine ⟨model_tuple, tuple_model, ?_, ?_⟩
  · rintro first second tuple - first_encodes - second_encodes ⟨x, position⟩ original_owner
    change originals x = true at original_owner
    rw [first_encodes ⟨x, original_owner⟩ position, second_encodes ⟨x, original_owner⟩ position]
  · intro first second first_tuple second_tuple first_encodes second_encodes agree
    funext x
    apply value_eq_of_bits csp x.val
    intro position
    have at_bit := agree ⟨x.val, position⟩ x.property
    rw [first_encodes x position, second_encodes x position] at at_bit
    exact at_bit

theorem valuation_of_assignment_block_eq_iff (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (first second : assignment csp) (h : Fin vertex_count) :
    (∀ variable_name, block_owner csp ladder_on variable_name = h →
      valuation_of_assignment csp ladder_on first variable_name =
        valuation_of_assignment csp ladder_on second variable_name) ↔ first h = second h := by
  constructor
  · intro agree
    have at_value := (agree (Sum.inl ⟨h, first h⟩) rfl).symm
    simpa [valuation_of_assignment] using at_value
  · intro same
    rintro (⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩) owner_is
    · change x = h at owner_is
      subst owner_is
      simp [valuation_of_assignment, same]
    · change x = h at owner_is
      subst owner_is
      simp [valuation_of_assignment, same]

theorem block_fixed_iff_of_model_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (formula : cnf_formula (boolean_variable csp all_vertices))
    (model_iff : ∀ valuation, is_model valuation formula ↔
      ∃ candidate, is_solution csp candidate ∧
        valuation = valuation_of_assignment csp all_vertices candidate)
    (tuple : original_tuple csp originals) (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (block_owner csp all_vertices) formula
        (encodes_tuple csp originals all_vertices) tuple h ↔
      extensions_agree_on csp originals tuple h := by
  constructor
  · intro fixed first second first_solution first_restricts second_solution second_restricts
    apply (valuation_of_assignment_block_eq_iff csp all_vertices first second h).mp
    apply fixed
    · exact (model_iff _).mpr ⟨first, first_solution, rfl⟩
    · rw [← first_restricts]
      exact valuation_of_assignment_encodes csp originals all_vertices first
    · exact (model_iff _).mpr ⟨second, second_solution, rfl⟩
    · rw [← second_restricts]
      exact valuation_of_assignment_encodes csp originals all_vertices second
  · intro agree first second first_model first_encodes second_model second_encodes
    obtain ⟨first_candidate, first_solution, rfl⟩ := (model_iff first).mp first_model
    obtain ⟨second_candidate, second_solution, rfl⟩ := (model_iff second).mp second_model
    have first_restricts : restrict_to_originals csp originals first_candidate = tuple :=
      encodes_tuple_unique csp originals all_vertices _ _ _
        (valuation_of_assignment_encodes csp originals all_vertices first_candidate) first_encodes
    have second_restricts : restrict_to_originals csp originals second_candidate = tuple :=
      encodes_tuple_unique csp originals all_vertices _ _ _
        (valuation_of_assignment_encodes csp originals all_vertices second_candidate)
        second_encodes
    exact (valuation_of_assignment_block_eq_iff csp all_vertices first_candidate second_candidate
      h).mpr (agree first_candidate second_candidate first_solution first_restricts
        second_solution second_restricts)

theorem support_block_fixed_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals)
    (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (block_owner csp all_vertices) (support_encoding csp)
        (encodes_tuple csp originals all_vertices) tuple h ↔
      extensions_agree_on csp originals tuple h :=
  block_fixed_iff_of_model_iff csp originals (support_encoding csp) (support_model_iff csp) tuple h

theorem direct_block_fixed_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tuple : original_tuple csp originals)
    (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (block_owner csp all_vertices) (direct_encoding csp)
        (encodes_tuple csp originals all_vertices) tuple h ↔
      extensions_agree_on csp originals tuple h :=
  block_fixed_iff_of_model_iff csp originals (direct_encoding csp) (direct_model_iff csp) tuple h

theorem min_eo_block_fixed_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (tuple : original_tuple csp originals)
    (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (block_owner csp all_vertices) (min_eo_encoding csp order)
        (encodes_tuple csp originals all_vertices) tuple h ↔
      extensions_agree_on csp originals tuple h :=
  block_fixed_iff_of_model_iff csp originals (min_eo_encoding csp order)
    (min_eo_model_iff csp order tree_order) tuple h

theorem log_block_fixed_iff (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
    (tuple : original_tuple csp originals) (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (bit_owner csp) (log_encoding csp)
        (log_encodes_tuple csp originals) tuple h ↔
      extensions_agree_on csp originals tuple h := by
  constructor
  · intro fixed first second first_solution first_restricts second_solution second_restricts
    apply value_eq_of_bits csp h
    intro position
    have first_encodes : log_encodes_tuple csp originals (log_valuation_of_assignment csp first)
        tuple := by
      rw [← first_restricts]
      exact log_valuation_of_assignment_encodes csp originals first
    have second_encodes : log_encodes_tuple csp originals
        (log_valuation_of_assignment csp second) tuple := by
      rw [← second_restricts]
      exact log_valuation_of_assignment_encodes csp originals second
    exact fixed (log_valuation_of_assignment csp first) (log_valuation_of_assignment csp second)
      ((log_model_iff csp _).mpr ⟨first, first_solution, rfl⟩) first_encodes
      ((log_model_iff csp _).mpr ⟨second, second_solution, rfl⟩) second_encodes
      ⟨h, position⟩ rfl
  · intro agree first second first_model first_encodes second_model second_encodes
    obtain ⟨first_candidate, first_solution, rfl⟩ := (log_model_iff csp first).mp first_model
    obtain ⟨second_candidate, second_solution, rfl⟩ := (log_model_iff csp second).mp second_model
    have first_restricts : restrict_to_originals csp originals first_candidate = tuple :=
      log_encodes_tuple_unique csp originals _ _ _
        (log_valuation_of_assignment_encodes csp originals first_candidate) first_encodes
    have second_restricts : restrict_to_originals csp originals second_candidate = tuple :=
      log_encodes_tuple_unique csp originals _ _ _
        (log_valuation_of_assignment_encodes csp originals second_candidate) second_encodes
    have same := agree first_candidate second_candidate first_solution first_restricts
      second_solution second_restricts
    rintro ⟨x, position⟩ owner_is
    change x = h at owner_is
    subst owner_is
    simp [log_valuation_of_assignment, same]

theorem partial_support_block_fixed_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) (tuple : original_tuple csp originals)
    (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (block_owner csp originals)
        (partial_support_encoding csp originals) (encodes_tuple csp originals originals) tuple h ↔
      extensions_agree_on csp originals tuple h := by
  constructor
  · intro fixed first second first_solution first_restricts second_solution second_restricts
    apply (valuation_of_assignment_block_eq_iff csp originals first second h).mp
    apply fixed
    · exact valuation_of_solution_is_partial_support_model csp originals first first_solution
    · rw [← first_restricts]
      exact valuation_of_assignment_encodes csp originals originals first
    · exact valuation_of_solution_is_partial_support_model csp originals second second_solution
    · rw [← second_restricts]
      exact valuation_of_assignment_encodes csp originals originals second
  · intro agree first second first_model first_encodes second_model second_encodes
    obtain ⟨first_extensions, first_union⟩ :=
      (partial_support_models_are_unions csp originals tree has_original tuple first).mp
        ⟨first_model, first_encodes⟩
    obtain ⟨second_extensions, second_union⟩ :=
      (partial_support_models_are_unions csp originals tree has_original tuple second).mp
        ⟨second_model, second_encodes⟩
    obtain ⟨first_member, first_member_in⟩ := first_union.1
    obtain ⟨second_member, second_member_in⟩ := second_union.1
    have value_iff : ∀ (union : boolean_variable csp originals → Bool)
        (extensions : Set (assignment csp)),
        is_union_of_extensions csp originals tuple union extensions →
        ∀ member ∈ extensions, ∀ a, union (Sum.inl ⟨h, a⟩) = decide (a = member h) := by
      intro union extensions union_is member member_in a
      have member_ok := union_is.2.1 member member_in
      apply Bool.eq_iff_iff.mpr
      rw [union_is.2.2.1 h a, decide_eq_true_iff]
      constructor
      · rintro ⟨other, other_in, other_at⟩
        have other_ok := union_is.2.1 other other_in
        rw [← other_at]
        exact agree other member other_ok.1 other_ok.2 member_ok.1 member_ok.2
      · intro a_is
        exact ⟨member, member_in, a_is.symm⟩
    have members_agree : first_member h = second_member h :=
      agree first_member second_member (first_union.2.1 first_member first_member_in).1
        (first_union.2.1 first_member first_member_in).2
        (second_union.2.1 second_member second_member_in).1
        (second_union.2.1 second_member second_member_in).2
    rintro (⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩) owner_is
    · change x = h at owner_is
      subst owner_is
      rw [value_iff first first_extensions first_union first_member first_member_in a,
        value_iff second second_extensions second_union second_member second_member_in a,
        members_agree]
    · rw [first_union.2.2.2 ⟨x, on_x⟩ i, second_union.2.2.2 ⟨x, on_x⟩ i]

theorem minimal_support_block_fixed_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple)
    (h : Fin vertex_count) :
    block_fixed_by_tuple csp originals (block_owner csp originals)
        (minimal_support_encoding csp originals order) (encodes_tuple csp originals originals)
        tuple h ↔
      ∃! a, in_upward_set csp originals order tuple h a := by
  obtain ⟨extension, extension_solution, extension_restricted⟩ := in_rel
  have extension_upward : in_upward_set csp originals order tuple h (extension h) := by
    have upward := extension_in_upward_set csp originals order tree_order extension
      extension_solution h
    rw [extension_restricted] at upward
    exact upward
  have singleton_model := valuation_of_solution_is_minimal_support_model csp originals order
    extension extension_solution
  have singleton_encodes : encodes_tuple csp originals originals
      (valuation_of_assignment csp originals extension) tuple := by
    rw [← extension_restricted]
    exact valuation_of_assignment_encodes csp originals originals extension
  obtain ⟨upward_model, upward_encodes⟩ := valuation_of_upward_sets_is_model csp originals order
    tree_order extension extension_solution
  rw [extension_restricted] at upward_model upward_encodes
  constructor
  · intro fixed
    refine ⟨extension h, extension_upward, ?_⟩
    intro other other_upward
    have at_other := fixed _ _ upward_model upward_encodes singleton_model singleton_encodes
      (Sum.inl ⟨h, other⟩) rfl
    simp [valuation_of_upward_sets, valuation_of_assignment, other_upward] at at_other
    exact at_other
  · rintro ⟨unique_value, _, unique_only⟩
    have selected_iff : ∀ valuation, is_model valuation (minimal_support_encoding csp originals order) →
        encodes_tuple csp originals originals valuation tuple →
        ∀ a, valuation (Sum.inl ⟨h, a⟩) = decide (a = unique_value) := by
      intro valuation model encodes a
      obtain ⟨active, active_selected⟩ := minimal_support_activation csp originals order tree_order
        root_original valuation model h
      have active_is : active = unique_value := unique_only active
        (selected_in_upward_set csp originals order tree_order tuple valuation model encodes h
          active active_selected)
      by_cases a_is : a = unique_value
      · rw [decide_eq_true a_is, a_is, ← active_is]
        exact active_selected
      · have not_selected : valuation (Sum.inl ⟨h, a⟩) ≠ true := fun a_selected =>
          a_is (unique_only a (selected_in_upward_set csp originals order tree_order tuple
            valuation model encodes h a a_selected))
        rw [decide_eq_false a_is]
        simpa using not_selected
    intro first second first_model first_encodes second_model second_encodes
    rintro (⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩) owner_is
    · change x = h at owner_is
      subst owner_is
      rw [selected_iff first first_model first_encodes a,
        selected_iff second second_model second_encodes a]
    · exact exactly_one_models_agree_on_originals csp originals originals first second tuple
        ((is_model_append first (exactly_one_part csp originals)
          (tree_order_support_clauses csp originals order)).mp first_model).1
        ((is_model_append second (exactly_one_part csp originals)
          (tree_order_support_clauses csp originals order)).mp second_model).1
        first_encodes second_encodes (Sum.inr ⟨⟨x, on_x⟩, i⟩) on_x

theorem minimal_support_single_value_block_fixed (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (tuple : original_tuple csp originals) (in_rel : in_relation csp originals tuple)
    (h : Fin vertex_count) (single_value : csp.domain_size h = 1) :
    block_fixed_by_tuple csp originals (block_owner csp originals)
      (minimal_support_encoding csp originals order) (encodes_tuple csp originals originals)
      tuple h := by
  rw [minimal_support_block_fixed_iff csp originals order tree_order root_original tuple in_rel h]
  obtain ⟨extension, extension_solution, extension_restricted⟩ := in_rel
  have extension_upward := extension_in_upward_set csp originals order tree_order extension
    extension_solution h
  rw [extension_restricted] at extension_upward
  refine ⟨extension h, extension_upward, ?_⟩
  intro other _
  apply Fin.ext
  have other_lt := other.isLt
  have extension_lt := (extension h).isLt
  omega

theorem ladder_bits_determine_value (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (h : Fin vertex_count) (on_h : ladder_on h = true)
    (first second : assignment csp)
    (same_ladder : ∀ i : Fin (csp.domain_size h - 1),
      valuation_of_assignment csp ladder_on first (Sum.inr ⟨⟨h, on_h⟩, i⟩) =
        valuation_of_assignment csp ladder_on second (Sum.inr ⟨⟨h, on_h⟩, i⟩)) :
    first h = second h := by
  have first_lt := (first h).isLt
  have second_lt := (second h).isLt
  rcases lt_trichotomy (first h).val (second h).val with smaller | same | larger
  · have at_rung := same_ladder ⟨(first h).val, by omega⟩
    simp [valuation_of_assignment] at at_rung
    omega
  · exact Fin.ext same
  · have at_rung := same_ladder ⟨(second h).val, by omega⟩
    simp [valuation_of_assignment] at at_rung
    omega

theorem support_keep_blocks_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (kept_hidden : Finset (Fin vertex_count)) :
    projected_count (support_encoding csp)
        (owned_variables (block_owner csp all_vertices)
          (original_vertices originals ∪ kept_hidden)) = relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        extensions_agree_on csp originals tuple h := by
  rw [keep_blocks_iff csp originals _ _ _ (support_original_coding csp originals)]
  simp only [support_block_fixed_iff]

theorem direct_keep_blocks_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (kept_hidden : Finset (Fin vertex_count)) :
    projected_count (direct_encoding csp)
        (owned_variables (block_owner csp all_vertices)
          (original_vertices originals ∪ kept_hidden)) = relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        extensions_agree_on csp originals tuple h := by
  rw [keep_blocks_iff csp originals _ _ _ (direct_original_coding csp originals)]
  simp only [direct_block_fixed_iff]

theorem min_eo_keep_blocks_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (kept_hidden : Finset (Fin vertex_count)) :
    projected_count (min_eo_encoding csp order)
        (owned_variables (block_owner csp all_vertices)
          (original_vertices originals ∪ kept_hidden)) = relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        extensions_agree_on csp originals tuple h := by
  rw [keep_blocks_iff csp originals _ _ _ (min_eo_original_coding csp originals order tree_order)]
  simp only [min_eo_block_fixed_iff csp originals order tree_order]

theorem log_keep_blocks_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (kept_hidden : Finset (Fin vertex_count)) :
    projected_count (log_encoding csp)
        (owned_variables (bit_owner csp) (original_vertices originals ∪ kept_hidden)) =
          relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        extensions_agree_on csp originals tuple h := by
  rw [keep_blocks_iff csp originals _ _ _ (log_original_coding csp originals)]
  simp only [log_block_fixed_iff]

theorem partial_support_keep_blocks_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (tree : is_binary_constraint_tree csp)
    (has_original : ∃ r, originals r = true) (kept_hidden : Finset (Fin vertex_count)) :
    projected_count (partial_support_encoding csp originals)
        (owned_variables (block_owner csp originals)
          (original_vertices originals ∪ kept_hidden)) = relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        extensions_agree_on csp originals tuple h := by
  rw [keep_blocks_iff csp originals _ _ _
    (partial_support_original_coding csp originals tree has_original)]
  simp only [partial_support_block_fixed_iff csp originals tree has_original]

theorem minimal_support_keep_blocks_iff (csp : binary_csp vertex_count)
    (originals : Fin vertex_count → Bool) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (root_original : root_is_original originals order)
    (kept_hidden : Finset (Fin vertex_count)) :
    projected_count (minimal_support_encoding csp originals order)
        (owned_variables (block_owner csp originals)
          (original_vertices originals ∪ kept_hidden)) = relation_count csp originals ↔
      ∀ tuple, in_relation csp originals tuple → ∀ h ∈ kept_hidden,
        ∃! a, in_upward_set csp originals order tuple h a := by
  rw [keep_blocks_iff csp originals _ _ _
    (minimal_support_original_coding csp originals order tree_order root_original)]
  constructor
  · intro fixed tuple in_rel h h_kept
    exact (minimal_support_block_fixed_iff csp originals order tree_order root_original tuple
      in_rel h).mp (fixed tuple in_rel h h_kept)
  · intro unique tuple in_rel h h_kept
    exact (minimal_support_block_fixed_iff csp originals order tree_order root_original tuple
      in_rel h).mpr (unique tuple in_rel h h_kept)

def solution_set (csp : binary_csp vertex_count) : Finset (assignment csp) :=
  Finset.univ.filter (is_solution csp)

def solution_pattern (csp : binary_csp vertex_count) (vertices : Finset (Fin vertex_count))
    (candidate : assignment csp) : ∀ x : Fin vertex_count, Option (Fin (csp.domain_size x)) :=
  fun x => if x ∈ vertices then some (candidate x) else none

def pattern_count (csp : binary_csp vertex_count) (vertices : Finset (Fin vertex_count)) : ℕ :=
  ((solution_set csp).image (solution_pattern csp vertices)).card

theorem solution_pattern_eq_iff (csp : binary_csp vertex_count)
    (vertices : Finset (Fin vertex_count)) (first second : assignment csp) :
    solution_pattern csp vertices first = solution_pattern csp vertices second ↔
      ∀ x ∈ vertices, first x = second x := by
  constructor
  · intro same x x_mem
    have at_x := congrFun same x
    simpa [solution_pattern, x_mem] using at_x
  · intro agree
    funext x
    by_cases x_mem : x ∈ vertices
    · simp [solution_pattern, x_mem, agree x x_mem]
    · simp [solution_pattern, x_mem]

theorem card_image_eq_of_same_kernel {item_type first_type second_type : Type}
    [DecidableEq first_type] [DecidableEq second_type] (items : Finset item_type)
    (first_map : item_type → first_type) (second_map : item_type → second_type)
    (same_kernel : ∀ first ∈ items, ∀ second ∈ items,
      first_map first = first_map second ↔ second_map first = second_map second) :
    (items.image first_map).card = (items.image second_map).card := by
  refine Finset.card_bij
    (fun image_value image_mem => second_map (Classical.choose (Finset.mem_image.mp image_mem)))
    ?_ ?_ ?_
  · intro image_value image_mem
    exact Finset.mem_image_of_mem second_map
      (Classical.choose_spec (Finset.mem_image.mp image_mem)).1
  · intro first_value first_mem second_value second_mem same_image
    have first_spec := Classical.choose_spec (Finset.mem_image.mp first_mem)
    have second_spec := Classical.choose_spec (Finset.mem_image.mp second_mem)
    exact first_spec.2.symm.trans
      (((same_kernel _ first_spec.1 _ second_spec.1).mpr same_image).trans second_spec.2)
  · intro target target_mem
    obtain ⟨item, item_mem, rfl⟩ := Finset.mem_image.mp target_mem
    refine ⟨first_map item, Finset.mem_image_of_mem first_map item_mem, ?_⟩
    have spec := Classical.choose_spec
      (Finset.mem_image.mp (Finset.mem_image_of_mem first_map item_mem))
    exact (same_kernel _ spec.1 _ item_mem).mp spec.2

theorem projected_count_eq_pattern_count {boolean_type : Type} [DecidableEq boolean_type]
    [Fintype boolean_type] (csp : binary_csp vertex_count) (formula : cnf_formula boolean_type)
    (valuation_of : assignment csp → boolean_type → Bool)
    (model_iff : ∀ valuation, is_model valuation formula ↔
      ∃ candidate, is_solution csp candidate ∧ valuation = valuation_of candidate)
    (kept : Finset boolean_type) (vertices : Finset (Fin vertex_count))
    (agree_iff : ∀ first second : assignment csp,
      (∀ variable_name ∈ kept, valuation_of first variable_name = valuation_of second variable_name) ↔
        ∀ x ∈ vertices, first x = second x) :
    projected_count formula kept = pattern_count csp vertices := by
  have models_eq : model_set formula = (solution_set csp).image valuation_of := by
    ext valuation
    simp only [model_set, solution_set, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    rw [model_iff valuation]
    constructor
    · rintro ⟨candidate, solution, rfl⟩
      exact ⟨candidate, solution, rfl⟩
    · rintro ⟨candidate, solution, rfl⟩
      exact ⟨candidate, solution, rfl⟩
  unfold projected_count projected_models pattern_count
  rw [models_eq, Finset.image_image]
  apply card_image_eq_of_same_kernel
  intro first _ second _
  simp only [Function.comp_apply]
  rw [masked_restriction_eq_iff, solution_pattern_eq_iff]
  exact agree_iff first second

theorem valuation_agree_on_blocks_iff (csp : binary_csp vertex_count)
    (ladder_on : Fin vertex_count → Bool) (vertices : Finset (Fin vertex_count))
    (first second : assignment csp) :
    (∀ variable_name ∈ owned_variables (block_owner csp ladder_on) vertices,
        valuation_of_assignment csp ladder_on first variable_name =
          valuation_of_assignment csp ladder_on second variable_name) ↔
      ∀ x ∈ vertices, first x = second x := by
  constructor
  · intro agree x x_mem
    have at_value := (agree (Sum.inl ⟨x, first x⟩)
      (by simp only [owned_variables, Finset.mem_filter, Finset.mem_univ, true_and]; exact x_mem)).symm
    simpa [valuation_of_assignment] using at_value
  · intro agree
    rintro (⟨x, a⟩ | ⟨⟨x, on_x⟩, i⟩) owned
    · have x_mem : x ∈ vertices := by
        simp only [owned_variables, Finset.mem_filter, Finset.mem_univ, true_and] at owned
        exact owned
      simp [valuation_of_assignment, agree x x_mem]
    · have x_mem : x ∈ vertices := by
        simp only [owned_variables, Finset.mem_filter, Finset.mem_univ, true_and] at owned
        exact owned
      simp [valuation_of_assignment, agree x x_mem]

theorem log_valuation_agree_on_blocks_iff (csp : binary_csp vertex_count)
    (vertices : Finset (Fin vertex_count)) (first second : assignment csp) :
    (∀ variable_name ∈ owned_variables (bit_owner csp) vertices,
        log_valuation_of_assignment csp first variable_name =
          log_valuation_of_assignment csp second variable_name) ↔
      ∀ x ∈ vertices, first x = second x := by
  constructor
  · intro agree x x_mem
    apply value_eq_of_bits csp x
    intro position
    exact agree ⟨x, position⟩
      (by simp only [owned_variables, Finset.mem_filter, Finset.mem_univ, true_and]; exact x_mem)
  · intro agree
    rintro ⟨x, position⟩ owned
    have x_mem : x ∈ vertices := by
      simp only [owned_variables, Finset.mem_filter, Finset.mem_univ, true_and] at owned
      exact owned
    simp [log_valuation_of_assignment, agree x x_mem]

theorem support_projected_count (csp : binary_csp vertex_count)
    (vertices : Finset (Fin vertex_count)) :
    projected_count (support_encoding csp) (owned_variables (block_owner csp all_vertices) vertices) =
      pattern_count csp vertices :=
  projected_count_eq_pattern_count csp (support_encoding csp)
    (valuation_of_assignment csp all_vertices) (support_model_iff csp) _ vertices
    (valuation_agree_on_blocks_iff csp all_vertices vertices)

theorem direct_projected_count (csp : binary_csp vertex_count)
    (vertices : Finset (Fin vertex_count)) :
    projected_count (direct_encoding csp) (owned_variables (block_owner csp all_vertices) vertices) =
      pattern_count csp vertices :=
  projected_count_eq_pattern_count csp (direct_encoding csp)
    (valuation_of_assignment csp all_vertices) (direct_model_iff csp) _ vertices
    (valuation_agree_on_blocks_iff csp all_vertices vertices)

theorem min_eo_projected_count (csp : binary_csp vertex_count) (order : List (Fin vertex_count))
    (tree_order : is_tree_order csp order) (vertices : Finset (Fin vertex_count)) :
    projected_count (min_eo_encoding csp order)
        (owned_variables (block_owner csp all_vertices) vertices) =
      pattern_count csp vertices :=
  projected_count_eq_pattern_count csp (min_eo_encoding csp order)
    (valuation_of_assignment csp all_vertices) (min_eo_model_iff csp order tree_order) _ vertices
    (valuation_agree_on_blocks_iff csp all_vertices vertices)

theorem log_projected_count (csp : binary_csp vertex_count)
    (vertices : Finset (Fin vertex_count)) :
    projected_count (log_encoding csp) (owned_variables (bit_owner csp) vertices) =
      pattern_count csp vertices :=
  projected_count_eq_pattern_count csp (log_encoding csp) (log_valuation_of_assignment csp)
    (log_model_iff csp) _ vertices (log_valuation_agree_on_blocks_iff csp vertices)

namespace counterexamples

def drop_example_csp : binary_csp 3 :=
  csp_of_edges 3 [1, 2, 2] [(0, 1, [(0, 0), (0, 1)]), (1, 2, [(0, 0), (1, 1)])] (by decide)
    (by decide)

theorem drop_example_order_is_valid : is_tree_order drop_example_csp [0, 1, 2] := by
  decide +kernel

theorem drop_example_relation_count :
    relation_count drop_example_csp first_vertex_is_original = 1 := by
  decide +kernel

theorem drop_example_extension_count :
    extension_count drop_example_csp first_vertex_is_original
      (fun x => ⟨0, drop_example_csp.domain_nonempty x.val⟩) = 2 := by
  decide +kernel

theorem drop_example_pattern_counts :
    pattern_count drop_example_csp {0, 1, 2} = 2 ∧ pattern_count drop_example_csp {0, 2} = 2 ∧
      pattern_count drop_example_csp {0, 1} = 2 ∧ pattern_count drop_example_csp {0} = 1 := by
  decide +kernel

theorem drop_example_support_counts :
    projected_count (support_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 1, 2}) = 2 ∧
      projected_count (support_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 2}) = 2 ∧
      projected_count (support_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 1}) = 2 ∧
      projected_count (support_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0}) = 1 := by
  simp only [support_projected_count]
  exact drop_example_pattern_counts

theorem drop_example_direct_counts :
    projected_count (direct_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 1, 2}) = 2 ∧
      projected_count (direct_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 2}) = 2 ∧
      projected_count (direct_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 1}) = 2 ∧
      projected_count (direct_encoding drop_example_csp)
        (owned_variables (block_owner drop_example_csp all_vertices) {0}) = 1 := by
  simp only [direct_projected_count]
  exact drop_example_pattern_counts

theorem drop_example_min_eo_counts :
    projected_count (min_eo_encoding drop_example_csp [0, 1, 2])
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 1, 2}) = 2 ∧
      projected_count (min_eo_encoding drop_example_csp [0, 1, 2])
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 2}) = 2 ∧
      projected_count (min_eo_encoding drop_example_csp [0, 1, 2])
        (owned_variables (block_owner drop_example_csp all_vertices) {0, 1}) = 2 ∧
      projected_count (min_eo_encoding drop_example_csp [0, 1, 2])
        (owned_variables (block_owner drop_example_csp all_vertices) {0}) = 1 := by
  simp only [min_eo_projected_count drop_example_csp [0, 1, 2] drop_example_order_is_valid]
  exact drop_example_pattern_counts

theorem drop_example_log_counts :
    projected_count (log_encoding drop_example_csp)
        (owned_variables (bit_owner drop_example_csp) {0, 1, 2}) = 2 ∧
      projected_count (log_encoding drop_example_csp)
        (owned_variables (bit_owner drop_example_csp) {0, 2}) = 2 ∧
      projected_count (log_encoding drop_example_csp)
        (owned_variables (bit_owner drop_example_csp) {0, 1}) = 2 ∧
      projected_count (log_encoding drop_example_csp)
        (owned_variables (bit_owner drop_example_csp) {0}) = 1 := by
  simp only [log_projected_count]
  exact drop_example_pattern_counts

theorem drop_example_partial_support_counts :
    projected_count (partial_support_encoding drop_example_csp first_vertex_is_original)
        (owned_variables (block_owner drop_example_csp first_vertex_is_original) {0, 1, 2}) = 3 ∧
      projected_count (partial_support_encoding drop_example_csp first_vertex_is_original)
        (owned_variables (block_owner drop_example_csp first_vertex_is_original) {0, 2}) = 3 ∧
      projected_count (partial_support_encoding drop_example_csp first_vertex_is_original)
        (owned_variables (block_owner drop_example_csp first_vertex_is_original) {0, 1}) = 3 ∧
      projected_count (partial_support_encoding drop_example_csp first_vertex_is_original)
        (owned_variables (block_owner drop_example_csp first_vertex_is_original) {0}) = 1 := by
  decide +kernel

end counterexamples

end parsimony
