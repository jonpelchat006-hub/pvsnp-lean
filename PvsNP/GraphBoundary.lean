/-!
# Discrete boundaries of labelled graphs

Sources: structural-reasoning/theory/folding/FOLDING_OUTLINE.md and
Desktop Vesica AI/AI Detector/planet/voidsearch.py (`cut` and `query`).
We isolate the discrete cut: an edge crosses when its endpoint labels differ.
An edge list is permitted to contain duplicates and either edge orientation;
adjacency is undirected. No spectral claim, geometric distance, or numerical
eigensolver correctness is assumed. In particular a sign-changing edge does
not imply there is a zero-valued vertex; a continuous interpolant would be
an additional object with additional hypotheses.
-/

namespace PvsNP.GraphBoundary

variable {Vertex Code : Type}

abbrev Edges (Vertex : Type) := List (Vertex × Vertex)

def crosses (label : Vertex → Bool) (edge : Vertex × Vertex) : Bool :=
  label edge.1 != label edge.2

/-- The edge boundary, retaining order and multiplicity from the source list. -/
def boundary (label : Vertex → Bool) (edges : Edges Vertex) : Edges Vertex :=
  edges.filter (crosses label)

def Adjacent (edges : Edges Vertex) (u v : Vertex) : Prop :=
  (u,v) ∈ edges ∨ (v,u) ∈ edges

def pathEdges : Vertex → List Vertex → Edges Vertex
  | _, [] => []
  | u, v :: rest => (u,v) :: pathEdges v rest

def endpoint : Vertex → List Vertex → Vertex
  | u, [] => u
  | _, v :: rest => endpoint v rest

/-- Every successive pair in the vertex sequence is adjacent in the graph. -/
def Walk (edges : Edges Vertex) (start : Vertex) (rest : List Vertex) : Prop :=
  ∀ e ∈ pathEdges start rest, Adjacent edges e.1 e.2

theorem crosses_iff (label : Vertex → Bool) (u v : Vertex) :
    crosses label (u,v) = true ↔ label u ≠ label v := by
  simp [crosses]

theorem mem_boundary_iff (label : Vertex → Bool) (edges : Edges Vertex)
    (e : Vertex × Vertex) :
    e ∈ boundary label edges ↔ e ∈ edges ∧ label e.1 ≠ label e.2 := by
  simp [boundary, crosses]

theorem crosses_reverse (label : Vertex → Bool) (u v : Vertex) :
    crosses label (v,u) = crosses label (u,v) := by
  change (label v != label u) = (label u != label v)
  cases label u <;> cases label v <;> rfl

theorem crosses_complement (label : Vertex → Bool) (e : Vertex × Vertex) :
    crosses (fun v => !(label v)) e = crosses label e := by
  change ((!label e.1) != (!label e.2)) = (label e.1 != label e.2)
  cases label e.1 <;> cases label e.2 <;> rfl

/-- Swapping the two domains leaves exactly the same boundary list. -/
theorem boundary_complement (label : Vertex → Bool) (edges : Edges Vertex) :
    boundary (fun v => !(label v)) edges = boundary label edges := by
  have hfun : crosses (fun v => !(label v)) = crosses label :=
    funext (crosses_complement label)
  simp only [boundary, hfun]

/-- Equal labels along each successive edge imply equal endpoint labels.
    This concerns the traversed path edges; unrelated graph edges may cross. -/
theorem same_labels_of_no_path_boundary (label : Vertex → Bool)
    (start : Vertex) (rest : List Vertex)
    (h : boundary label (pathEdges start rest) = []) :
    label start = label (endpoint start rest) := by
  induction rest generalizing start with
  | nil => rfl
  | cons next rest ih =>
    have hc : label start = label next := by
      by_cases he : label start = label next
      · exact he
      · have hm : (start,next) ∈ boundary label (pathEdges start (next::rest)) :=
          (mem_boundary_iff _ _ _).2 ⟨by simp [pathEdges], he⟩
        simp [h] at hm
    have ht : boundary label (pathEdges next rest) = [] := by
      simpa [boundary, pathEdges, crosses, hc] using h
    exact hc.trans (ih next ht)

/-- A path between different labels must cross somewhere on that path. -/
theorem path_boundary_nonempty_of_separated_endpoints (label : Vertex → Bool)
    (start : Vertex) (rest : List Vertex)
    (h : label start ≠ label (endpoint start rest)) :
    boundary label (pathEdges start rest) ≠ [] :=
  fun hz => h (same_labels_of_no_path_boundary label start rest hz)

/-- Each crossing traversed by a walk is an edge of the graph boundary,
    after choosing the orientation in which the graph recorded that edge. -/
theorem graph_boundary_of_path_boundary (label : Vertex → Bool)
    {edges : Edges Vertex} {start : Vertex} {rest : List Vertex}
    (hw : Walk edges start rest) {u v : Vertex}
    (he : (u,v) ∈ boundary label (pathEdges start rest)) :
    (u,v) ∈ boundary label edges ∨ (v,u) ∈ boundary label edges := by
  obtain ⟨hp, hc⟩ := (mem_boundary_iff _ _ _).1 he
  obtain h | h := hw (u,v) hp
  · exact Or.inl ((mem_boundary_iff _ _ _).2 ⟨h, hc⟩)
  · exact Or.inr ((mem_boundary_iff _ _ _).2 ⟨h, Ne.symm hc⟩)

/-- Different endpoint labels on a walk force a nonempty graph boundary. -/
theorem graph_boundary_nonempty_of_separated_walk (label : Vertex → Bool)
    {edges : Edges Vertex} {start : Vertex} {rest : List Vertex}
    (hw : Walk edges start rest)
    (h : label start ≠ label (endpoint start rest)) :
    boundary label edges ≠ [] := by
  have hp := path_boundary_nonempty_of_separated_endpoints label start rest h
  obtain ⟨⟨u,v⟩, he⟩ := List.exists_mem_of_ne_nil _ hp
  obtain hc | hc := graph_boundary_of_path_boundary label hw he
  · intro hz
    simp [hz] at hc
  · intro hz
    simp [hz] at hc

/-- A label readable from a representation has the same crossing test
    on the represented endpoints. The representation need not be injective. -/
theorem crosses_of_factor (encode : Vertex → Code) (label : Vertex → Bool)
    (decode : Code → Bool) (hd : ∀ v, decode (encode v) = label v)
    (u v : Vertex) :
    crosses decode (encode u,encode v) = crosses label (u,v) := by
  simp [crosses, hd]

/-- Encoding commutes with extracting the boundary if the labels factor
    through that encoding; duplicates are preserved on both sides. -/
theorem boundary_map_of_factor (encode : Vertex → Code) (label : Vertex → Bool)
    (decode : Code → Bool) (hd : ∀ v, decode (encode v) = label v)
    (edges : Edges Vertex) :
    boundary decode (edges.map (fun e => (encode e.1,encode e.2))) =
      (boundary label edges).map (fun e => (encode e.1,encode e.2)) := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    unfold boundary at *
    simp only [List.map_cons, List.filter_cons, crosses, hd]
    split <;> simp_all

/-- The Python split uses f < 0 for one side and f >= 0 for the other. -/
def negativeSide (value : Vertex → Int) (v : Vertex) : Bool := decide (value v < 0)

def twoVertexValue (v : Bool) : Int := if v then 1 else -1

/-- A graph with one opposite-sign edge and no zero-valued vertex.
    A discrete boundary is therefore different from a zero-vertex set. -/
theorem opposite_sign_edge_without_zero :
    twoVertexValue false < 0 ∧ 0 < twoVertexValue true ∧
    boundary (negativeSide twoVertexValue) [(false,true)] = [(false,true)] ∧
    ∀ v, twoVertexValue v ≠ 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro v
  cases v <;> decide

end PvsNP.GraphBoundary
