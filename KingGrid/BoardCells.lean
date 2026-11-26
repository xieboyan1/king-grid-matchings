import KingGrid.BoardCuts
namespace BoardCells
open BoardCuts

-- Match the equality test used by List.perm_iff_count.
local instance : BEq Cell := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq Cell where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

theorem block_count (i j : Nat) (x : Cell) :
    (block i j).count x = if x.1 / 2 = i ∧ x.2 / 2 = j then 1 else 0 := by
  obtain ⟨r,c⟩ := x
  simp only [block, List.count_cons, List.count_nil, beq_iff_eq, Prod.mk.injEq]
  split <;> split <;> split <;> split <;> split <;> simp_all <;> omega

theorem band_count (i n : Nat) (x : Cell) :
    (band i n).count x = if x.1 / 2 = i ∧ x.2 < 2*n then 1 else 0 := by
  induction n with
  | zero => simp [band]
  | succ n ih =>
    rw [band, List.count_append, ih, block_count]
    split <;> split <;> split <;> omega

theorem board_count (m n : Nat) (x : Cell) :
    (board n m).count x = if x.1 < 2*m ∧ x.2 < 2*n then 1 else 0 := by
  induction m with
  | zero => simp [board]
  | succ m ih =>
    rw [board, List.count_append, ih, band_count]
    split <;> split <;> split <;> omega

def swapCell (x : Cell) : Cell := (x.2,x.1)
def swapEdge (e : Edge) : Edge := (swapCell e.1, swapCell e.2)

theorem swapCell_twice (x : Cell) : swapCell (swapCell x) = x := rfl
theorem swapEdge_twice (e : Edge) : swapEdge (swapEdge e) = e := rfl

theorem swap_count (xs : List Cell) (x : Cell) :
    (xs.map swapCell).count x = xs.count (swapCell x) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq]
    by_cases e : swapCell y = x
    · have g : y = swapCell x := congrArg swapCell e
      simp [e,g,swapCell_twice]
    · have g : y ≠ swapCell x := fun h => e (congrArg swapCell h)
      simp [e,g]

theorem transpose_board (m n : Nat) : ((board n m).map swapCell).Perm (board m n) := by
  apply List.perm_iff_count.mpr
  intro x
  rw [swap_count, board_count, board_count]
  simp [swapCell, and_comm]

theorem transpose_ends (es : List Edge) : ends (es.map swapEdge) = (ends es).map swapCell := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ends,swapEdge,ih]

theorem transpose_tiling (m n : Nat) {es : List Edge} (h : Tiling m n es) :
    Tiling n m (es.map swapEdge) := by
  constructor
  · rw [transpose_ends]
    exact (h.1.map _).trans (transpose_board m n)
  · intro e he
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp he
    obtain ⟨ne,r,c⟩ := h.2 z hz
    exact ⟨fun h' => ne (congrArg swapCell h'),c,r⟩

theorem transpose_h (es : List Edge) :
    (es.map swapEdge).countP (flat Prod.fst) = es.countP (flat Prod.snd) := by
  rw [List.countP_map]
  rfl

theorem transpose_v (es : List Edge) :
    (es.map swapEdge).countP (flat Prod.snd) = es.countP (flat Prod.fst) := by
  rw [List.countP_map]
  rfl

#print axioms board_count
#print axioms transpose_tiling
end BoardCells
