import parsimony.lower_bound
import parsimony.counterexamples

namespace parsimony

variable {vertex_count : ℕ}

section recurrence

open Classical

variable (csp : binary_csp vertex_count) (originals : Fin vertex_count → Bool)
  (order : List (Fin vertex_count)) (tuple : original_tuple csp originals)

noncomputable def upward_values (z : Fin vertex_count) : Finset (Fin (csp.domain_size z)) :=
  Finset.univ.filter fun a => in_upward_set csp originals order tuple z a

def is_admissible (z : Fin vertex_count) (chosen : Finset (Fin (csp.domain_size z))) : Prop :=
  (∀ on_z : originals z = true, chosen = {tuple ⟨z, on_z⟩}) ∧
    (originals z = false → chosen.Nonempty ∧ chosen ⊆ upward_values csp originals order tuple z)

def supports_set (p z : Fin vertex_count) (upper : Finset (Fin (csp.domain_size p)))
    (lower : Finset (Fin (csp.domain_size z))) : Prop :=
  ∀ a ∈ upper, ∃ b ∈ lower, csp.allowed p z a b = true

def is_completion (top : Fin vertex_count) (top_set : Finset (Fin (csp.domain_size top)))
    (family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z))) : Prop :=
  family top = top_set ∧
    (∀ z, z ≠ top → ¬ is_below csp order top z → family z = ∅) ∧
    (∀ z, is_below csp order top z → is_admissible csp originals order tuple z (family z)) ∧
    ∀ p z, is_below csp order top z → csp.adjacent p z = true → earlier_in order p z = true →
      supports_set csp p z (family p) (family z)

noncomputable def completion_count (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top))) : ℕ :=
  Fintype.card {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
    is_completion csp originals order tuple top top_set family}

noncomputable def children_of (top : Fin vertex_count) : Finset (Fin vertex_count) :=
  Finset.univ.filter fun y => csp.adjacent top y = true ∧ earlier_in order top y = true

noncomputable def admissible_supported (top y : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top))) : Finset (Finset (Fin (csp.domain_size y))) :=
  Finset.univ.filter fun chosen =>
    is_admissible csp originals order tuple y chosen ∧ supports_set csp top y top_set chosen

def is_child_completion (top : Fin vertex_count) (top_set : Finset (Fin (csp.domain_size top)))
    (y : Fin vertex_count) (family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z))) :
    Prop :=
  is_completion csp originals order tuple y (family y) family ∧
    is_admissible csp originals order tuple y (family y) ∧ supports_set csp top y top_set (family y)

noncomputable def restrict_to_branch (family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)))
    (y : Fin vertex_count) : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) :=
  fun z => if z = y ∨ is_below csp order y z then family z else ∅

theorem is_below_trans (top middle z : Fin vertex_count)
    (below_middle : is_below csp order top middle) (below_z : is_below csp order middle z) :
    is_below csp order top z := by
  induction below_z with
  | child y adjacent_middle_y middle_earlier =>
    exact is_below.step middle y below_middle adjacent_middle_y middle_earlier
  | step x y _ adjacent_x_y x_earlier below_x =>
    exact is_below.step x y below_x adjacent_x_y x_earlier

theorem below_ne_top (top z : Fin vertex_count) (below : is_below csp order top z) : z ≠ top := by
  intro same
  have position := is_below_position csp order top z below
  rw [same] at position
  exact lt_irrefl _ position

theorem branch_exists (top z : Fin vertex_count) (below : is_below csp order top z) :
    ∃ y, csp.adjacent top y = true ∧ earlier_in order top y = true ∧
      (z = y ∨ is_below csp order y z) := by
  induction below with
  | child y adjacent_top_y top_earlier => exact ⟨y, adjacent_top_y, top_earlier, Or.inl rfl⟩
  | step x y _ adjacent_x_y x_earlier branch_x =>
    obtain ⟨child, adjacent_child, child_earlier, x_in_branch⟩ := branch_x
    refine ⟨child, adjacent_child, child_earlier, Or.inr ?_⟩
    rcases x_in_branch with x_is_child | below_child_x
    · rw [← x_is_child]
      exact is_below.child y adjacent_x_y x_earlier
    · exact is_below.step x y below_child_x adjacent_x_y x_earlier

theorem branch_unique (tree_order : is_tree_order csp order) (top first second : Fin vertex_count)
    (first_adjacent : csp.adjacent top first = true) (first_earlier : earlier_in order top first = true)
    (second_adjacent : csp.adjacent top second = true)
    (second_earlier : earlier_in order top second = true) (z : Fin vertex_count)
    (in_first : z = first ∨ is_below csp order first z)
    (in_second : z = second ∨ is_below csp order second z) : first = second := by
  have child_not_below : ∀ child other : Fin vertex_count,
      csp.adjacent top child = true → earlier_in order top child = true →
      earlier_in order top other = true → ¬ is_below csp order other child := by
    intro child other adjacent_child child_earlier other_earlier below_other
    rcases parent_of_below csp order tree_order other top child below_other adjacent_child
        child_earlier with top_is_other | below_top
    · have top_lt : order.idxOf top < order.idxOf other := by simpa [earlier_in] using other_earlier
      rw [top_is_other] at top_lt
      exact lt_irrefl _ top_lt
    · have other_lt := is_below_position csp order other top below_top
      have top_lt : order.idxOf top < order.idxOf other := by simpa [earlier_in] using other_earlier
      omega
  have by_position : ∀ position z, order.idxOf z = position →
      (z = first ∨ is_below csp order first z) → (z = second ∨ is_below csp order second z) →
      first = second := by
    intro position
    induction position using Nat.strong_induction_on with
    | _ position inductive_case =>
      intro z z_position z_in_first z_in_second
      rcases z_in_first with z_is_first | below_first
      · rcases z_in_second with z_is_second | below_second
        · rw [← z_is_first, ← z_is_second]
        · rw [z_is_first] at below_second
          exact absurd below_second
            (child_not_below first second first_adjacent first_earlier second_earlier)
      · rcases z_in_second with z_is_second | below_second
        · rw [z_is_second] at below_first
          exact absurd below_first
            (child_not_below second first second_adjacent second_earlier first_earlier)
        · have first_lt := is_below_position csp order first z below_first
          obtain ⟨parent, parent_adjacent, parent_lt, _⟩ :=
            tree_order_unique_earlier_neighbour csp order tree_order z (by omega)
          have parent_earlier : earlier_in order parent z = true := by
            simpa [earlier_in] using parent_lt
          exact inductive_case (order.idxOf parent) (by omega) parent rfl
            (parent_of_below csp order tree_order first parent z below_first parent_adjacent
              parent_earlier)
            (parent_of_below csp order tree_order second parent z below_second parent_adjacent
              parent_earlier)
  exact by_position _ z rfl in_first in_second

theorem below_head (tree_order : is_tree_order csp order) (root : Fin vertex_count)
    (root_first : order.idxOf root = 0) (z : Fin vertex_count) (z_ne_root : z ≠ root) :
    is_below csp order root z := by
  have by_position : ∀ position z, order.idxOf z = position → z ≠ root →
      is_below csp order root z := by
    intro position
    induction position using Nat.strong_induction_on with
    | _ position inductive_case =>
      intro z z_position z_ne_root
      have z_positive : 0 < order.idxOf z := by
        rcases Nat.eq_zero_or_pos (order.idxOf z) with zero | positive
        · exact absurd ((List.idxOf_inj (tree_order.2.1 z)).mp (zero.trans root_first.symm))
            z_ne_root
        · exact positive
      obtain ⟨parent, parent_adjacent, parent_lt, _⟩ :=
        tree_order_unique_earlier_neighbour csp order tree_order z z_positive
      have parent_earlier : earlier_in order parent z = true := by
        simpa [earlier_in] using parent_lt
      by_cases parent_is_root : parent = root
      · rw [parent_is_root] at parent_adjacent parent_earlier
        exact is_below.child z parent_adjacent parent_earlier
      · exact is_below.step parent z
          (inductive_case (order.idxOf parent) (by omega) parent rfl parent_is_root)
          parent_adjacent parent_earlier
  exact by_position _ z rfl z_ne_root

theorem sup_of_single {index_type : Type} [Fintype index_type] [DecidableEq index_type]
    {element_type : Type} [DecidableEq element_type] (pieces : index_type → Finset element_type)
    (chosen : index_type) (others_empty : ∀ i, i ≠ chosen → pieces i = ∅) :
    Finset.univ.sup pieces = pieces chosen := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    by_cases i_is_chosen : i = chosen
    · rw [i_is_chosen]
    · rw [others_empty i i_is_chosen]
      exact Finset.empty_subset _
  · exact Finset.le_sup (Finset.mem_univ chosen)

theorem sup_of_empty {index_type : Type} [Fintype index_type] [DecidableEq index_type]
    {element_type : Type} [DecidableEq element_type] (pieces : index_type → Finset element_type)
    (all_empty : ∀ i, pieces i = ∅) : Finset.univ.sup pieces = ∅ := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    rw [all_empty i]
  · exact Finset.empty_subset _

noncomputable def combine_branches (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (parts : ∀ y : {y // y ∈ children_of csp order top},
      {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_child_completion csp originals order tuple top top_set y.1 family}) :
    ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) :=
  Function.update (fun z => Finset.univ.sup fun y => (parts y).1 z) top top_set

theorem mem_children_of (top y : Fin vertex_count) :
    y ∈ children_of csp order top ↔ csp.adjacent top y = true ∧ earlier_in order top y = true := by
  simp [children_of]

theorem branch_is_below (top y z : Fin vertex_count) (y_child : y ∈ children_of csp order top)
    (in_branch : z = y ∨ is_below csp order y z) : is_below csp order top z := by
  obtain ⟨adjacent_top_y, top_earlier⟩ := (mem_children_of csp order top y).mp y_child
  rcases in_branch with z_is_y | below_y
  · rw [z_is_y]
    exact is_below.child y adjacent_top_y top_earlier
  · exact is_below_trans csp order top y z (is_below.child y adjacent_top_y top_earlier) below_y

theorem part_outside_branch (top : Fin vertex_count) (top_set : Finset (Fin (csp.domain_size top)))
    (y : Fin vertex_count) (family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)))
    (child_completion : is_child_completion csp originals order tuple top top_set y family)
    (z : Fin vertex_count) (outside : ¬ (z = y ∨ is_below csp order y z)) : family z = ∅ :=
  child_completion.1.2.1 z (fun z_is_y => outside (Or.inl z_is_y))
    (fun below_y => outside (Or.inr below_y))

theorem combine_at_branch (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (parts : ∀ y : {y // y ∈ children_of csp order top},
      {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_child_completion csp originals order tuple top top_set y.1 family})
    (y : {y // y ∈ children_of csp order top}) (z : Fin vertex_count)
    (in_branch : z = y.1 ∨ is_below csp order y.1 z) :
    combine_branches csp originals order tuple top top_set parts z = (parts y).1 z := by
  have z_ne_top : z ≠ top :=
    below_ne_top csp order top z (branch_is_below csp order top y.1 z y.2 in_branch)
  rw [combine_branches, Function.update_of_ne z_ne_top]
  apply sup_of_single
  intro other other_ne_y
  apply part_outside_branch csp originals order tuple top top_set other.1 (parts other).1
    (parts other).2 z
  intro in_other
  obtain ⟨adjacent_other, other_earlier⟩ := (mem_children_of csp order top other.1).mp other.2
  obtain ⟨adjacent_y, y_earlier⟩ := (mem_children_of csp order top y.1).mp y.2
  exact other_ne_y (Subtype.ext (branch_unique csp order tree_order top other.1 y.1 adjacent_other
    other_earlier adjacent_y y_earlier z in_other in_branch))

theorem combine_outside (top : Fin vertex_count) (top_set : Finset (Fin (csp.domain_size top)))
    (parts : ∀ y : {y // y ∈ children_of csp order top},
      {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_child_completion csp originals order tuple top top_set y.1 family})
    (z : Fin vertex_count) (z_ne_top : z ≠ top) (not_below : ¬ is_below csp order top z) :
    combine_branches csp originals order tuple top top_set parts z = ∅ := by
  rw [combine_branches, Function.update_of_ne z_ne_top]
  apply sup_of_empty
  intro y
  apply part_outside_branch csp originals order tuple top top_set y.1 (parts y).1 (parts y).2 z
  intro in_branch
  exact not_below (branch_is_below csp order top y.1 z y.2 in_branch)

theorem combine_is_completion (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (parts : ∀ y : {y // y ∈ children_of csp order top},
      {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_child_completion csp originals order tuple top top_set y.1 family}) :
    is_completion csp originals order tuple top top_set
      (combine_branches csp originals order tuple top top_set parts) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [combine_branches]
  · intro z z_ne_top not_below
    exact combine_outside csp originals order tuple top top_set parts z z_ne_top not_below
  · intro z below_top
    obtain ⟨y, adjacent_y, y_earlier, in_branch⟩ := branch_exists csp order top z below_top
    have y_child : y ∈ children_of csp order top := (mem_children_of csp order top y).mpr
      ⟨adjacent_y, y_earlier⟩
    rw [combine_at_branch csp originals order tuple tree_order top top_set parts ⟨y, y_child⟩ z
      in_branch]
    rcases in_branch with z_is_y | below_y
    · subst z_is_y
      exact (parts ⟨z, y_child⟩).2.2.1
    · exact (parts ⟨y, y_child⟩).2.1.2.2.1 z below_y
  · intro p z below_top adjacent_p_z p_earlier
    obtain ⟨y, adjacent_y, y_earlier, in_branch⟩ := branch_exists csp order top z below_top
    have y_child : y ∈ children_of csp order top := (mem_children_of csp order top y).mpr
      ⟨adjacent_y, y_earlier⟩
    rw [combine_at_branch csp originals order tuple tree_order top top_set parts ⟨y, y_child⟩ z
      in_branch]
    rcases in_branch with z_is_y | below_y
    · have p_is_top : p = top := by
        rw [z_is_y] at adjacent_p_z p_earlier
        exact earlier_neighbour_unique csp order tree_order y p top adjacent_p_z p_earlier
          adjacent_y y_earlier
      subst z_is_y
      subst p_is_top
      have top_value : combine_branches csp originals order tuple p top_set parts p = top_set := by
        simp [combine_branches]
      rw [top_value]
      exact (parts ⟨z, y_child⟩).2.2.2
    · have p_in_branch : p = y ∨ is_below csp order y p :=
        parent_of_below csp order tree_order y p z below_y adjacent_p_z p_earlier
      rw [combine_at_branch csp originals order tuple tree_order top top_set parts ⟨y, y_child⟩ p
        p_in_branch]
      exact (parts ⟨y, y_child⟩).2.1.2.2.2 p z below_y adjacent_p_z p_earlier

theorem restrict_is_child_completion (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)))
    (completion : is_completion csp originals order tuple top top_set family)
    (y : Fin vertex_count) (y_child : y ∈ children_of csp order top) :
    is_child_completion csp originals order tuple top top_set y
      (restrict_to_branch csp order family y) := by
  obtain ⟨adjacent_y, y_earlier⟩ := (mem_children_of csp order top y).mp y_child
  have below_top_y : is_below csp order top y := is_below.child y adjacent_y y_earlier
  have at_y : restrict_to_branch csp order family y y = family y := by
    simp [restrict_to_branch]
  have inside : ∀ z, is_below csp order y z → restrict_to_branch csp order family y z = family z := by
    intro z below_y
    simp [restrict_to_branch, below_y]
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z z_ne_y not_below
    simp [restrict_to_branch, z_ne_y, not_below]
  · intro z below_y
    rw [inside z below_y]
    exact completion.2.2.1 z (is_below_trans csp order top y z below_top_y below_y)
  · intro p z below_y adjacent_p_z p_earlier
    rw [inside z below_y]
    have p_in_branch := parent_of_below csp order tree_order y p z below_y adjacent_p_z p_earlier
    have at_p : restrict_to_branch csp order family y p = family p := by
      rcases p_in_branch with p_is_y | below_p
      · rw [p_is_y]
        exact at_y
      · exact inside p below_p
    rw [at_p]
    exact completion.2.2.2 p z (is_below_trans csp order top y z below_top_y below_y) adjacent_p_z
      p_earlier
  · rw [at_y]
    exact completion.2.2.1 y below_top_y
  · rw [at_y, ← completion.1]
    exact completion.2.2.2 top y below_top_y adjacent_y y_earlier

theorem combine_restrict (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)))
    (completion : is_completion csp originals order tuple top top_set family) :
    combine_branches csp originals order tuple top top_set
      (fun y => ⟨restrict_to_branch csp order family y.1,
        restrict_is_child_completion csp originals order tuple tree_order top top_set family
          completion y.1 y.2⟩) = family := by
  funext z
  by_cases z_is_top : z = top
  · subst z_is_top
    simp [combine_branches, completion.1]
  · by_cases below_top : is_below csp order top z
    · obtain ⟨y, adjacent_y, y_earlier, in_branch⟩ := branch_exists csp order top z below_top
      have y_child : y ∈ children_of csp order top := (mem_children_of csp order top y).mpr
        ⟨adjacent_y, y_earlier⟩
      rw [combine_at_branch csp originals order tuple tree_order top top_set _ ⟨y, y_child⟩ z
        in_branch]
      simp [restrict_to_branch, in_branch]
    · rw [combine_outside csp originals order tuple top top_set _ z z_is_top below_top]
      exact (completion.2.1 z z_is_top below_top).symm

theorem restrict_combine (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (parts : ∀ y : {y // y ∈ children_of csp order top},
      {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_child_completion csp originals order tuple top top_set y.1 family})
    (y : {y // y ∈ children_of csp order top}) :
    restrict_to_branch csp order (combine_branches csp originals order tuple top top_set parts) y.1 =
      (parts y).1 := by
  funext z
  by_cases in_branch : z = y.1 ∨ is_below csp order y.1 z
  · rw [restrict_to_branch, ite_eq_left in_branch]
    exact combine_at_branch csp originals order tuple tree_order top top_set parts y z in_branch
  · rw [restrict_to_branch, ite_eq_right in_branch]
    exact (part_outside_branch csp originals order tuple top top_set y.1 (parts y).1 (parts y).2 z
      in_branch).symm

noncomputable def completion_split (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top))) :
    {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_completion csp originals order tuple top top_set family} ≃
      ∀ y : {y // y ∈ children_of csp order top},
        {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
          is_child_completion csp originals order tuple top top_set y.1 family} where
  toFun family := fun y => ⟨restrict_to_branch csp order family.1 y.1,
    restrict_is_child_completion csp originals order tuple tree_order top top_set family.1 family.2
      y.1 y.2⟩
  invFun parts := ⟨combine_branches csp originals order tuple top top_set parts,
    combine_is_completion csp originals order tuple tree_order top top_set parts⟩
  left_inv family := Subtype.ext (combine_restrict csp originals order tuple tree_order top top_set
    family.1 family.2)
  right_inv parts := funext fun y => Subtype.ext (restrict_combine csp originals order tuple
    tree_order top top_set parts y)

noncomputable def child_completion_by_top_set (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top))) (y : Fin vertex_count) :
    {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_child_completion csp originals order tuple top top_set y family} ≃
      Σ chosen : {chosen // chosen ∈ admissible_supported csp originals order tuple top y top_set},
        {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
          is_completion csp originals order tuple y chosen.1 family} where
  toFun family := ⟨⟨family.1 y, by simp [admissible_supported, family.2.2.1, family.2.2.2]⟩,
    ⟨family.1, family.2.1⟩⟩
  invFun pair := ⟨pair.2.1, by
    have at_y : pair.2.1 y = pair.1.1 := pair.2.2.1
    have member := pair.1.2
    simp only [admissible_supported, Finset.mem_filter, Finset.mem_univ, true_and] at member
    refine ⟨?_, ?_, ?_⟩
    · rw [at_y]
      exact pair.2.2
    · rw [at_y]
      exact member.1
    · rw [at_y]
      exact member.2⟩
  left_inv family := rfl
  right_inv pair := by
    obtain ⟨⟨chosen, member⟩, ⟨family, completion⟩⟩ := pair
    have at_y : family y = chosen := completion.1
    subst at_y
    rfl

theorem completion_count_recurrence (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top))) :
    completion_count csp originals order tuple top top_set =
      ∏ y ∈ children_of csp order top,
        ∑ chosen ∈ admissible_supported csp originals order tuple top y top_set,
          completion_count csp originals order tuple y chosen := by
  unfold completion_count
  rw [Fintype.card_congr (completion_split csp originals order tuple tree_order top top_set),
    Fintype.card_pi, ← Finset.prod_coe_sort (children_of csp order top)]
  apply Finset.prod_congr rfl
  intro y _
  rw [Fintype.card_congr (child_completion_by_top_set csp originals order tuple top top_set y.1),
    Fintype.card_sigma, ← Finset.sum_coe_sort (admissible_supported csp originals order tuple top y.1
      top_set)]

theorem completion_count_of_leaf (tree_order : is_tree_order csp order) (top : Fin vertex_count)
    (top_set : Finset (Fin (csp.domain_size top)))
    (leaf : ∀ y, csp.adjacent top y = true → earlier_in order top y = false) :
    completion_count csp originals order tuple top top_set = 1 := by
  rw [completion_count_recurrence csp originals order tuple tree_order top top_set]
  have no_children : children_of csp order top = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro y y_child
    obtain ⟨adjacent_y, y_earlier⟩ := (mem_children_of csp order top y).mp y_child
    rw [leaf y adjacent_y] at y_earlier
    exact absurd y_earlier (by decide)
  rw [no_children, Finset.prod_empty]

noncomputable def selection_completion_equiv (tree_order : is_tree_order csp order)
    (root : Fin vertex_count) (root_head : order.head? = some root)
    (root_original : originals root = true) :
    {selected : ∀ x : Fin vertex_count, Fin (csp.domain_size x) → Bool //
        is_selection_over csp originals order tuple selected} ≃
      {family : ∀ z : Fin vertex_count, Finset (Fin (csp.domain_size z)) //
        is_completion csp originals order tuple root {tuple ⟨root, root_original⟩} family} where
  toFun selection := ⟨fun z => Finset.univ.filter fun a => selection.1 z a = true, by
    have root_first : order.idxOf root = 0 := index_zero_of_head order root root_head
    have model := valuation_of_selection_is_model csp originals order tuple selection.1 selection.2
    have encodes := valuation_of_selection_encodes csp originals order tuple selection.1 selection.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext a
      simp [selection.2.1 root root_original a]
    · intro z z_ne_root not_below
      exact absurd (below_head csp order tree_order root root_first z z_ne_root) not_below
    · intro z _
      refine ⟨?_, ?_⟩
      · intro on_z
        ext a
        simp [selection.2.1 z on_z a]
      · intro _
        refine ⟨?_, ?_⟩
        · obtain ⟨a, a_selected⟩ := minimal_support_activation csp originals order tree_order
            ⟨root, root_head, root_original⟩ _ model z
          exact ⟨a, by simpa [valuation_of_selection] using a_selected⟩
        · intro a a_member
          have a_selected : selection.1 z a = true := by simpa using a_member
          have upward := selected_in_upward_set csp originals order tree_order tuple _ model encodes z a
            (by simpa [valuation_of_selection] using a_selected)
          simpa [upward_values] using upward
    · intro p z _ adjacent_p_z p_earlier a a_member
      have a_selected : selection.1 p a = true := by simpa using a_member
      obtain ⟨b, b_allowed, b_selected⟩ := selection.2.2 p z adjacent_p_z p_earlier a a_selected
      exact ⟨b, by simpa using b_selected, b_allowed⟩⟩
  invFun completion := ⟨fun z a => decide (a ∈ completion.1 z), by
    have root_first : order.idxOf root = 0 := index_zero_of_head order root root_head
    refine ⟨?_, ?_⟩
    · intro x on_x a
      show decide (a ∈ completion.1 x) = decide (a = tuple ⟨x, on_x⟩)
      by_cases x_is_root : x = root
      · subst x_is_root
        rw [completion.2.1]
        simp
      · have admissible := completion.2.2.2.1 x
          (below_head csp order tree_order root root_first x x_is_root)
        rw [admissible.1 on_x]
        simp
    · intro x y adjacent_x_y x_earlier a a_selected
      have y_ne_root : y ≠ root := by
        intro y_is_root
        have x_lt : order.idxOf x < order.idxOf y := by simpa [earlier_in] using x_earlier
        rw [y_is_root, root_first] at x_lt
        exact Nat.not_lt_zero _ x_lt
      have supported := completion.2.2.2.2 x y
        (below_head csp order tree_order root root_first y y_ne_root) adjacent_x_y x_earlier a
        (by simpa using a_selected)
      obtain ⟨b, b_member, b_allowed⟩ := supported
      exact ⟨b, b_allowed, by simpa using b_member⟩⟩
  left_inv selection := by
    apply Subtype.ext
    funext z a
    simp
  right_inv completion := by
    apply Subtype.ext
    funext z
    ext a
    simp

theorem minimal_support_models_eq_root_completion_count (tree_order : is_tree_order csp order)
    (root : Fin vertex_count) (root_head : order.head? = some root)
    (root_original : originals root = true) :
    models_over_tuple csp originals originals (minimal_support_encoding csp originals order) tuple =
      completion_count csp originals order tuple root {tuple ⟨root, root_original⟩} := by
  rw [minimal_support_models_over_tuple_eq_selection_count]
  unfold completion_count
  exact Fintype.card_congr (selection_completion_equiv csp originals order tuple tree_order root
    root_head root_original)

end recurrence

def recurrence_smallest_tuple :
    original_tuple counterexamples.smallest_csp counterexamples.first_vertex_is_original :=
  fun x => ⟨0, counterexamples.smallest_csp.domain_nonempty x.1⟩

theorem recurrence_smallest_models_over_tuple :
    models_over_tuple counterexamples.smallest_csp counterexamples.first_vertex_is_original
      counterexamples.first_vertex_is_original
      (minimal_support_encoding counterexamples.smallest_csp counterexamples.first_vertex_is_original
        [0, 1])
      recurrence_smallest_tuple = 2 := by
  decide +kernel

theorem recurrence_smallest_root_completion_count :
    completion_count counterexamples.smallest_csp counterexamples.first_vertex_is_original [0, 1]
      recurrence_smallest_tuple 0 {recurrence_smallest_tuple ⟨0, rfl⟩} = 2 := by
  rw [← minimal_support_models_eq_root_completion_count counterexamples.smallest_csp
    counterexamples.first_vertex_is_original [0, 1] recurrence_smallest_tuple
    counterexamples.smallest_order_is_valid 0 rfl rfl]
  exact recurrence_smallest_models_over_tuple

end parsimony
