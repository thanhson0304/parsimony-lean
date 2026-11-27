import parsimony.tree_order
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace parsimony

variable {vertex_count : ℕ}

theorem is_tree_order_of_unique_earlier (csp : binary_csp vertex_count)
    (order : List (Fin vertex_count)) (order_nodup : order.Nodup)
    (order_complete : ∀ x, x ∈ order)
    (unique_earlier : ∀ x, 0 < order.idxOf x →
      ∃ parent, csp.adjacent parent x = true ∧ order.idxOf parent < order.idxOf x ∧
        ∀ other, csp.adjacent other x = true → order.idxOf other < order.idxOf x →
          other = parent) :
    is_tree_order csp order := by
  refine ⟨order_nodup, order_complete, ?_⟩
  intro later later_positive
  have position_of_later : order.idxOf (order.get later) = later.val :=
    List.Nodup.idxOf_getElem order_nodup later.val later.isLt
  obtain ⟨parent, parent_adjacent, parent_earlier, parent_unique⟩ :=
    unique_earlier (order.get later) (by omega)
  rw [List.countP_eq_length_filter]
  have filter_nodup : ((order.take later.val).filter
      (fun earlier_vertex => csp.adjacent earlier_vertex (order.get later))).Nodup :=
    (order_nodup.sublist (List.take_sublist _ _)).filter _
  rw [← List.toFinset_card_of_nodup filter_nodup]
  have as_singleton : ((order.take later.val).filter
      (fun earlier_vertex => csp.adjacent earlier_vertex (order.get later))).toFinset =
      {parent} := by
    ext z
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨z_in_take, z_adjacent⟩
      have z_earlier := (List.mem_take_iff_idxOf_lt (order_complete z)).mp z_in_take
      exact parent_unique z z_adjacent (by omega)
    · intro z_is_parent
      subst z_is_parent
      exact ⟨(List.mem_take_iff_idxOf_lt (order_complete z)).mpr (by omega), parent_adjacent⟩
  rw [as_singleton, Finset.card_singleton]

theorem closer_neighbour_gives_concat {vertex_type : Type} {graph : SimpleGraph vertex_type}
    (tree : graph.IsTree) (root v w : vertex_type) (path_to_v : graph.Walk root v)
    (is_path : path_to_v.IsPath) (path_length : path_to_v.length = graph.dist root v)
    (adjacent : graph.Adj w v) (closer : graph.dist root w + 1 = graph.dist root v) :
    ∃ path_to_w : graph.Walk root w, path_to_v = path_to_w.concat adjacent := by
  obtain ⟨path_to_w, w_is_path, w_length⟩ :=
    (tree.connected root w).exists_path_of_dist
  by_cases w_on_path : w ∈ path_to_v.support
  · exact ⟨path_to_w, tree.isAcyclic.path_concat w_is_path is_path adjacent w_on_path⟩
  · exfalso
    have v_on_path : v ∈ path_to_w.support :=
      tree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath w_is_path is_path adjacent
        w_on_path
    have as_concat := tree.isAcyclic.path_concat is_path w_is_path adjacent.symm v_on_path
    have longer : path_to_w.length = path_to_v.length + 1 := by
      rw [as_concat, SimpleGraph.Walk.length_concat]
    omega

theorem closer_neighbour_exists_unique {vertex_type : Type} {graph : SimpleGraph vertex_type}
    (tree : graph.IsTree) (root v : vertex_type) (v_ne_root : v ≠ root) :
    ∃ w, graph.Adj w v ∧ graph.dist root w + 1 = graph.dist root v ∧
      ∀ other, graph.Adj other v → graph.dist root other + 1 = graph.dist root v → other = w := by
  obtain ⟨walk_to_root, walk_length⟩ := tree.connected.exists_walk_length_eq_dist v root
  obtain ⟨w, adjacent_v_w, rest, walk_is⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne v_ne_root walk_to_root
  have rest_bound : graph.dist w root ≤ rest.length := SimpleGraph.dist_le rest
  have walk_cons : walk_to_root.length = rest.length + 1 := by
    rw [walk_is, SimpleGraph.Walk.length_cons]
  have w_closer : graph.dist root w + 1 = graph.dist root v := by
    have one_step := tree.dist_eq_dist_add_one_of_adj root adjacent_v_w
    rw [SimpleGraph.dist_comm (u := w) (v := root)] at rest_bound
    rw [SimpleGraph.dist_comm (u := v) (v := root)] at walk_length
    omega
  obtain ⟨path_to_v, is_path, path_length⟩ := (tree.connected root v).exists_path_of_dist
  refine ⟨w, adjacent_v_w.symm, w_closer, ?_⟩
  intro other other_adjacent other_closer
  obtain ⟨path_to_w, w_concat⟩ := closer_neighbour_gives_concat tree root v w path_to_v is_path
    path_length adjacent_v_w.symm w_closer
  obtain ⟨path_to_other, other_concat⟩ := closer_neighbour_gives_concat tree root v other path_to_v
    is_path path_length other_adjacent other_closer
  have both := other_concat.symm.trans w_concat
  obtain ⟨same_vertex, _⟩ := SimpleGraph.Walk.concat_inj both
  exact same_vertex

theorem exists_tree_order_with_root (csp : binary_csp vertex_count)
    (tree : is_binary_constraint_tree csp) (root : Fin vertex_count) :
    ∃ order, is_tree_order csp order ∧ order.idxOf root = 0 := by
  classical
  have graph_tree : (constraint_graph csp).IsTree := tree
  let distance : Fin vertex_count → ℕ := fun x => (constraint_graph csp).dist root x
  let closer_or_equal : Fin vertex_count → Fin vertex_count → Bool :=
    fun first second => decide (distance first ≤ distance second)
  let order := (List.finRange vertex_count).mergeSort closer_or_equal
  have order_perm : order.Perm (List.finRange vertex_count) :=
    List.mergeSort_perm _ _
  have order_nodup : order.Nodup := order_perm.nodup_iff.mpr (List.nodup_finRange _)
  have order_complete : ∀ x, x ∈ order :=
    fun x => order_perm.mem_iff.mpr (List.mem_finRange x)
  have order_sorted : order.Pairwise (fun first second => closer_or_equal first second = true) :=
    List.pairwise_mergeSort
      (fun first second third first_le second_le => by
        simp only [closer_or_equal, decide_eq_true_eq] at first_le second_le ⊢
        omega)
      (fun first second => by
        simp only [closer_or_equal, Bool.or_eq_true, decide_eq_true_eq]
        omega)
      _
  have position_bound : ∀ x, order.idxOf x < order.length :=
    fun x => List.idxOf_lt_length_iff.mpr (order_complete x)
  have monotone : ∀ x y, order.idxOf x < order.idxOf y → distance x ≤ distance y := by
    intro x y x_earlier
    have sorted_at := (List.pairwise_iff_getElem.mp order_sorted) (order.idxOf x) (order.idxOf y)
      (position_bound x) (position_bound y) x_earlier
    simp only [List.getElem_idxOf] at sorted_at
    simpa [closer_or_equal] using sorted_at
  have positions_differ : ∀ x y, x ≠ y → order.idxOf x ≠ order.idxOf y := by
    intro x y x_ne_y same_position
    exact x_ne_y ((List.idxOf_inj (order_complete x)).mp same_position)
  have root_distance : distance root = 0 := SimpleGraph.dist_self
  have root_first : order.idxOf root = 0 := by
    by_contra not_first
    have root_positive : 0 < order.idxOf root := Nat.pos_of_ne_zero not_first
    have first_bound : 0 < order.length := by have := position_bound root; omega
    let first_vertex := order[0]
    have first_position : order.idxOf first_vertex = 0 :=
      List.Nodup.idxOf_getElem order_nodup 0 first_bound
    have first_close := monotone first_vertex root (by omega)
    have first_is_root : root = first_vertex := by
      apply graph_tree.connected.dist_eq_zero_iff.mp
      show distance first_vertex = 0
      omega
    rw [first_is_root, first_position] at not_first
    exact not_first rfl
  refine ⟨order, is_tree_order_of_unique_earlier csp order order_nodup order_complete ?_, root_first⟩
  intro x x_positive
  have x_ne_root : x ≠ root := by
    intro x_is_root
    rw [x_is_root, root_first] at x_positive
    omega
  obtain ⟨parent, parent_adjacent, parent_closer, parent_unique⟩ :=
    closer_neighbour_exists_unique graph_tree root x x_ne_root
  have parent_ne_x : parent ≠ x := (constraint_graph csp).ne_of_adj parent_adjacent
  refine ⟨parent, parent_adjacent, ?_, ?_⟩
  · have differ := positions_differ parent x parent_ne_x
    by_contra not_earlier
    have x_earlier : order.idxOf x < order.idxOf parent := by omega
    have close := monotone x parent x_earlier
    have closer : distance parent + 1 = distance x := parent_closer
    omega
  · intro other other_adjacent other_earlier
    have close := monotone other x other_earlier
    have one_step := graph_tree.dist_eq_dist_add_one_of_adj root
      (show (constraint_graph csp).Adj other x from other_adjacent)
    apply parent_unique other other_adjacent
    have close_as_dist : (constraint_graph csp).dist root other ≤
        (constraint_graph csp).dist root x := close
    omega

end parsimony
