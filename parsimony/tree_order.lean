import parsimony.definitions

namespace parsimony

variable {vertex_count : ℕ}

theorem tree_order_unique_earlier_neighbour (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
    (x : Fin vertex_count) (not_first : 0 < order.idxOf x) :
    ∃ parent, csp.adjacent parent x = true ∧ order.idxOf parent < order.idxOf x ∧
      ∀ other, csp.adjacent other x = true → order.idxOf other < order.idxOf x →
        other = parent := by
  obtain ⟨_, order_complete, one_earlier⟩ := tree_order
  have position_valid : order.idxOf x < order.length :=
    List.idxOf_lt_length_iff.mpr (order_complete x)
  have count_is_one := one_earlier ⟨order.idxOf x, position_valid⟩ not_first
  have get_is_x : order.get ⟨order.idxOf x, position_valid⟩ = x := by
    simp [List.getElem_idxOf]
  simp only [get_is_x] at count_is_one
  rw [List.countP_eq_length_filter] at count_is_one
  obtain ⟨parent, filter_is_parent⟩ := List.length_eq_one_iff.mp count_is_one
  have parent_in_filter : parent ∈ (order.take (order.idxOf x)).filter
      (fun earlier_vertex => csp.adjacent earlier_vertex x) := by
    rw [filter_is_parent]
    simp
  rw [List.mem_filter] at parent_in_filter
  refine ⟨parent, parent_in_filter.2, ?_, ?_⟩
  · exact (List.mem_take_iff_idxOf_lt (order_complete parent)).mp parent_in_filter.1
  · intro other other_adjacent other_earlier
    have other_in_take := (List.mem_take_iff_idxOf_lt (order_complete other)).mpr other_earlier
    have other_in_filter : other ∈ (order.take (order.idxOf x)).filter
        (fun earlier_vertex => csp.adjacent earlier_vertex x) :=
      List.mem_filter.mpr ⟨other_in_take, other_adjacent⟩
    rw [filter_is_parent] at other_in_filter
    simpa using other_in_filter

theorem tree_order_positions_differ (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
    (x y : Fin vertex_count) (x_ne_y : x ≠ y) : order.idxOf x ≠ order.idxOf y := by
  intro same_position
  exact x_ne_y ((List.idxOf_inj (tree_order.2.1 x)).mp same_position)

theorem tree_order_reachable_from_first (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
    (root : Fin vertex_count) (root_first : order.idxOf root = 0) (x : Fin vertex_count) :
    (constraint_graph csp).Reachable root x := by
  have by_position : ∀ position, ∀ y : Fin vertex_count, order.idxOf y = position →
      (constraint_graph csp).Reachable root y := by
    intro position
    induction position using Nat.strong_induction_on with
    | _ position inductive_case =>
      intro y y_position
      by_cases y_first : position = 0
      · have y_is_root : y = root := by
          by_contra y_ne_root
          exact tree_order_positions_differ csp order tree_order y root y_ne_root
            (by rw [y_position, root_first, y_first])
        rw [y_is_root]
      · obtain ⟨parent, parent_adjacent, parent_earlier, _⟩ :=
          tree_order_unique_earlier_neighbour csp order tree_order y (by omega)
        have parent_reachable :=
          inductive_case (order.idxOf parent) (by omega) parent rfl
        exact parent_reachable.trans (SimpleGraph.Adj.reachable parent_adjacent)
  exact by_position (order.idxOf x) x rfl

theorem tree_order_edge_count (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
    (root : Fin vertex_count) (root_first : order.idxOf root = 0) :
    Nat.card (constraint_graph csp).edgeSet + 1 = Nat.card (Fin vertex_count) := by
  classical
  let non_first := {x : Fin vertex_count // x ≠ root}
  have position_positive : ∀ x : non_first, 0 < order.idxOf x.val := by
    intro x
    have differ := tree_order_positions_differ csp order tree_order x.val root x.property
    omega
  choose parent_of parent_adjacent parent_earlier parent_unique using
    fun x : non_first =>
      tree_order_unique_earlier_neighbour csp order tree_order x.val (position_positive x)
  let edge_of : non_first → (constraint_graph csp).edgeSet := fun x =>
    ⟨s(parent_of x, x.val), by
      rw [SimpleGraph.mem_edgeSet]
      exact parent_adjacent x⟩
  have edge_of_injective : Function.Injective edge_of := by
    intro x y same_edge
    have same_pair := congrArg Subtype.val same_edge
    simp only [edge_of, Sym2.eq_iff] at same_pair
    rcases same_pair with ⟨_, same_vertex⟩ | ⟨parent_x_is_y, x_is_parent_y⟩
    · exact Subtype.ext same_vertex
    · have x_earlier := parent_earlier x
      have y_earlier := parent_earlier y
      rw [parent_x_is_y] at x_earlier
      rw [← x_is_parent_y] at y_earlier
      omega
  have edge_of_surjective : Function.Surjective edge_of := by
    rintro ⟨edge, edge_member⟩
    induction edge using Sym2.ind with
    | _ first_end second_end =>
      rw [SimpleGraph.mem_edgeSet] at edge_member
      have ends_differ : first_end ≠ second_end := (constraint_graph csp).ne_of_adj edge_member
      have positions_differ :=
        tree_order_positions_differ csp order tree_order first_end second_end ends_differ
      rcases Nat.lt_or_gt_of_ne positions_differ with first_earlier | second_earlier
      · have second_not_root : second_end ≠ root := by
          intro second_is_root
          rw [second_is_root, root_first] at first_earlier
          omega
        refine ⟨⟨second_end, second_not_root⟩, Subtype.ext ?_⟩
        have first_is_parent :=
          parent_unique ⟨second_end, second_not_root⟩ first_end edge_member first_earlier
        simp only [edge_of]
        rw [← first_is_parent]
      · have first_not_root : first_end ≠ root := by
          intro first_is_root
          rw [first_is_root, root_first] at second_earlier
          omega
        refine ⟨⟨first_end, first_not_root⟩, Subtype.ext ?_⟩
        have second_is_parent :=
          parent_unique ⟨first_end, first_not_root⟩ second_end edge_member.symm second_earlier
        simp only [edge_of]
        rw [← second_is_parent, Sym2.eq_swap]
  have same_card : Nat.card (constraint_graph csp).edgeSet = Nat.card non_first :=
    (Nat.card_congr (Equiv.ofBijective edge_of ⟨edge_of_injective, edge_of_surjective⟩)).symm
  have non_first_card : Fintype.card non_first = vertex_count - 1 := by
    simp [non_first]
  have root_is_vertex : 0 < vertex_count := root.pos
  rw [same_card, Nat.card_eq_fintype_card, non_first_card, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  omega

theorem is_binary_constraint_tree_of_tree_order (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (tree_order : is_tree_order csp order)
    (root : Fin vertex_count) (root_first : order.idxOf root = 0) :
    is_binary_constraint_tree csp := by
  rw [is_binary_constraint_tree, SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, tree_order_edge_count csp order tree_order root root_first⟩
  have : Nonempty (Fin vertex_count) := ⟨root⟩
  refine SimpleGraph.Connected.mk ?_
  intro x y
  exact (tree_order_reachable_from_first csp order tree_order root root_first x).symm.trans
    (tree_order_reachable_from_first csp order tree_order root root_first y)

end parsimony
