import KingGrid.BoardRoundtrip
import KingGrid.BoardCells

/- Count geometric matchings: two ordered lists of oriented edges describe
   the same object exactly when they induce the same unordered edge relation. -/
namespace KingEnumeration
open BoardCuts BoardCells StripCounts

abbrev Shape := Cell → Cell → Prop
def shape (es : List Edge) : Shape := fun x y => (x,y) ∈ es ∨ (y,x) ∈ es
def turn (R : Shape) : Shape := fun x y => R (swapCell x) (swapCell y)
theorem turn_turn (R : Shape) : turn (turn R) = R := rfl

theorem shape_transpose (es : List Edge) : shape (es.map swapEdge) = turn (shape es) := by
  have h (x y : Cell) : (x,y) ∈ es.map swapEdge ↔ (swapCell x,swapCell y) ∈ es := by
    constructor
    · intro ht
      obtain ⟨u,hu,he⟩ := List.mem_map.mp ht
      have eq : u = (swapCell x,swapCell y) := congrArg swapEdge he
      exact eq ▸ hu
    · intro ht
      exact List.mem_map.mpr ⟨_,ht,rfl⟩
  funext x y
  apply propext
  exact or_congr (h x y) (h y x)

def IsTwoTiling (m n : Nat) (R : Shape) : Prop :=
  ∃ es : List Edge, Tiling m n es ∧
    es.countP (flat Prod.fst) + es.countP (flat Prod.snd) = 2 ∧ R = shape es

theorem two_tiling_transpose {m n : Nat} {R : Shape} (h : IsTwoTiling m n R) :
    IsTwoTiling n m (turn R) := by
  obtain ⟨es,T,ct,rfl⟩ := h
  refine ⟨es.map swapEdge, transpose_tiling m n T, ?_, (shape_transpose es).symm⟩
  rw [transpose_h,transpose_v,Nat.add_comm]
  exact ct

def horizontalShape (m : Nat) (fs : StripFamily) : Shape := shape (StripPlacement.edges m fs)
def physical (m n : Nat) : Sum StripFamily StripFamily → Shape
  | .inl fs => horizontalShape m fs
  | .inr fs => turn (horizontalShape n fs)
def geometricTilings (m n : Nat) : List Shape :=
  (orientedMatchings m n).map (physical m n)

private theorem horizontal_spec {m n : Nat} {fs : StripFamily}
    (h : fs ∈ horizontalMatchings m n) : IsTwoTiling m n (horizontalShape m fs) := by
  obtain ⟨hl,hf,hc⟩ := (horizontal_membership _ _ _).mp h
  have T := StripPlacement.edges_valid m fs hf
  rw [hl] at T
  have z : (StripPlacement.edges m fs).countP (flat Prod.snd) = 0 := by
    apply List.countP_eq_zero.mpr
    intro e he
    simpa [flat] using StripPlacement.no_vertical m fs e he
  exact ⟨_,T,by rw [z, Nat.add_zero, StripPlacement.horizontal_count_edges, hc],rfl⟩

private theorem has_horizontal {m n : Nat} {fs : StripFamily} (h : fs ∈ horizontalMatchings m n) :
    ∃ x y, horizontalShape m fs x y ∧ x.1=y.1 := by
  have c := ((horizontal_membership _ _ _).mp h).2.2
  rw [← StripPlacement.horizontal_count_edges] at c
  have pos : 0 < (StripPlacement.edges m fs).countP (flat Prod.fst) := by omega
  obtain ⟨e,he,hf⟩ := List.countP_pos_iff.mp pos
  exact ⟨e.1,e.2,Or.inl he,by simpa [flat] using hf⟩

private theorem no_vertical (m : Nat) (fs : StripFamily) {x y : Cell}
    (h : horizontalShape m fs x y) : x.2 ≠ y.2 := by
  rcases h with h|h
  · exact StripPlacement.no_vertical m fs _ h
  · exact Ne.symm (StripPlacement.no_vertical m fs _ h)

private theorem cannot_turn {m n : Nat} {fs gs : StripFamily}
    (h : fs ∈ horizontalMatchings m n) :
    horizontalShape m fs ≠ turn (horizontalShape n gs) := by
  intro eq
  obtain ⟨x,y,he,hxy⟩ := has_horizontal h
  rw [eq] at he
  exact no_vertical n gs he hxy

private theorem horiz_injective {m n : Nat} {fs gs : StripFamily}
    (hf : fs ∈ horizontalMatchings m n) (hg : gs ∈ horizontalMatchings m n)
    (eq : horizontalShape m fs = horizontalShape m gs) : fs = gs := by
  obtain ⟨lf,vf,_⟩ := (horizontal_membership _ _ _).mp hf
  obtain ⟨lg,vg,_⟩ := (horizontal_membership _ _ _).mp hg
  apply StripPlacement.edges_faithful (m := m) (fs := fs) (gs := gs)
  all_goals first | exact lf.trans lg.symm | exact vf | exact vg |
    exact fun x y => Iff.of_eq (congrFun (congrFun eq x) y)

private theorem mem_left (m n : Nat) (fs : StripFamily) :
    Sum.inl fs ∈ orientedMatchings m n ↔ fs ∈ horizontalMatchings m n := by
  simp [orientedMatchings]
private theorem mem_right (m n : Nat) (fs : StripFamily) :
    Sum.inr fs ∈ orientedMatchings m n ↔ fs ∈ horizontalMatchings n m := by
  simp [orientedMatchings]

private theorem dedup_map {α β : Type} {xs : List α} {f : α → β} (hn : xs.Nodup)
    (inj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a=b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
      exact ha ((inj b (by simp [hb]) a (by simp) eq) ▸ hb)
    · exact ih hn (fun a ha b hb => inj _ (by simp [ha]) _ (by simp [hb]))

theorem no_duplicate_geometric_tilings (m n : Nat) : (geometricTilings m n).Nodup := by
  apply dedup_map (oriented_nodup m n)
  intro a ha b hb eq
  cases a with
  | inl fs =>
    have hf := (mem_left _ _ _).mp ha
    cases b with
    | inl gs => exact congrArg Sum.inl (horiz_injective hf ((mem_left _ _ _).mp hb) eq)
    | inr gs => exact False.elim (cannot_turn hf eq)
  | inr fs =>
    have hf := (mem_right _ _ _).mp ha
    cases b with
    | inr gs => exact congrArg Sum.inr (horiz_injective hf ((mem_right _ _ _).mp hb) (congrArg turn eq))
    | inl gs => exact False.elim (cannot_turn ((mem_left _ _ _).mp hb) eq.symm)

private theorem cover_horizontal {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (cv : es.countP (flat Prod.snd) = 0) (ch : es.countP (flat Prod.fst) = 2) :
    ∃ fs ∈ horizontalMatchings m n, horizontalShape m fs = shape es := by
  have nv (e) (he : e ∈ es) : e.1.2 ≠ e.2.2 := by
    simpa [flat] using List.countP_eq_zero.mp cv e he
  refine ⟨BoardEncoding.encode es m n,BoardEncoding.encode_horizontal T nv ch,?_⟩
  funext x y
  apply propext
  exact (BoardEncoding.encode_decode_same T nv x y).symm

theorem membership_iff_two_tiling (m n : Nat) (R : Shape) :
    R ∈ geometricTilings m n ↔ IsTwoTiling m n R := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    cases a with
    | inl fs => exact horizontal_spec ((mem_left _ _ _).mp ha)
    | inr gs => exact two_tiling_transpose (horizontal_spec ((mem_right _ _ _).mp ha))
  · rintro ⟨es,T,ct,rfl⟩
    apply List.mem_map.mpr
    rcases parallel_if_two m n es T ct with ch|cv
    · have ct' : (es.map swapEdge).countP (flat Prod.fst) = 2 := by rw [transpose_h]; omega
      have cz : (es.map swapEdge).countP (flat Prod.snd) = 0 := (transpose_v es).trans ch
      obtain ⟨gs,hg,eq⟩ := cover_horizontal (transpose_tiling m n T) cz ct'
      refine ⟨Sum.inr gs, (mem_right _ _ _).mpr hg, ?_⟩
      exact congrArg turn (eq.trans (shape_transpose es))
    · obtain ⟨fs,hf,eq⟩ := cover_horizontal T cv (by omega)
      exact ⟨Sum.inl fs, (mem_left _ _ _).mpr hf, eq⟩

/-- An actual list of pairwise distinct geometric edge relations, containing
    precisely the matchings of the whole rectangle with two axial edges. -/
theorem exactly_two_rectangle (m n : Nat) :
    ∃ tilings : List Shape, tilings.Nodup ∧ (∀ R, R ∈ tilings ↔ IsTwoTiling m n R) ∧
      2*tilings.length = n*(m*(m+1)) + m*(n*(n+1)) :=
  ⟨geometricTilings m n,no_duplicate_geometric_tilings m n,membership_iff_two_tiling m n,
   by simpa [geometricTilings] using oriented_count m n⟩

theorem exactly_two_square (n : Nat) :
    ∃ tilings : List Shape, tilings.Nodup ∧ (∀ R, R ∈ tilings ↔ IsTwoTiling n n R) ∧
      tilings.length = n*n*(n+1) :=
  ⟨geometricTilings n n,no_duplicate_geometric_tilings n n,membership_iff_two_tiling n n,
   by simpa [geometricTilings] using oriented_square_count n⟩

#print axioms exactly_two_rectangle
#print axioms exactly_two_square
end KingEnumeration
