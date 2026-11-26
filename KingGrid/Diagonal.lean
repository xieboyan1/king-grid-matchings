import Lean

/-!
Perfect matchings by diagonal king moves on an even rectangular board.
Rows and columns are zero-indexed. A tiling is represented by its partner
function on all cells. Legality rules out fixed points, and the involution
law says that the two cells of each pair choose one another.
-/
namespace DimerDiagonal

abbrev Board (m n : Nat) := Fin (2 * m) × Fin (2 * n)

def OneApart (i j : Nat) : Prop := i + 1 = j ∨ j + 1 = i

def DiagonalMove {m n : Nat} (x y : Board m n) : Prop :=
  OneApart x.1.val y.1.val ∧ OneApart x.2.val y.2.val

def IsDiagonalTiling {m n : Nat} (f : Board m n → Board m n) : Prop :=
  (∀ x, f (f x) = x) ∧ ∀ x, DiagonalMove x (f x)

/-- Exchange coordinates 0↔1, 2↔3, and so forth. -/
def flip (i : Nat) : Nat := if i % 2 = 0 then i + 1 else i - 1

private theorem flip_lt {m i : Nat} (hi : i < 2 * m) : flip i < 2 * m := by
  unfold flip
  split <;> omega

private theorem flip_twice (i : Nat) : flip (flip i) = i := by
  by_cases h : i % 2 = 0
  · have h' : (i + 1) % 2 ≠ 0 := by omega
    simp [flip, h, h']
  · have h' : (i - 1) % 2 = 0 := by omega
    simp only [flip, if_neg h, if_pos h']
    omega

def mate {m : Nat} (i : Fin (2 * m)) : Fin (2 * m) :=
  ⟨flip i.val, flip_lt i.isLt⟩

/-- Opposite corner of the cell's aligned 2×2 block. -/
def canonical {m n : Nat} (x : Board m n) : Board m n := (mate x.1, mate x.2)

private theorem canonical_twice {m n : Nat} (x : Board m n) :
    canonical (canonical x) = x := by
  apply Prod.ext
  · exact Fin.ext (flip_twice x.1.val)
  · exact Fin.ext (flip_twice x.2.val)

private theorem oneApart_flip (i : Nat) : OneApart i (flip i) := by
  unfold OneApart flip
  split <;> omega

theorem canonical_isTiling (m n : Nat) :
    IsDiagonalTiling (@canonical m n) :=
  ⟨canonical_twice, fun x => ⟨oneApart_flip x.1.val, oneApart_flip x.2.val⟩⟩

private def score (m i : Nat) : Nat :=
  if i % 2 = 0 then i else 2 * m - i

/-- Taking a legal step then flipping either returns to its starting point
or strictly lowers the parity-oriented coordinate score. -/
private theorem coordinate_descent (m i j : Nat)
    (hj : j < 2 * m) (h : OneApart i j) :
    flip j = i ∨ score m (flip j) < score m i := by
  rcases h with h | h
  · by_cases e : i % 2 = 0
    · have a : j % 2 ≠ 0 := by omega
      left
      simp only [flip, if_neg a]
      omega
    · have a : j % 2 = 0 := by omega
      have b : (j+1) % 2 ≠ 0 := by omega
      right
      simp only [flip, if_pos a, score, if_neg e, if_neg b]
      omega
  · by_cases e : i % 2 = 0
    · have a : j % 2 ≠ 0 := by omega
      have b : (j-1) % 2 = 0 := by omega
      right
      simp only [flip, if_neg a, score, if_pos e, if_pos b]
      omega
    · have a : j % 2 = 0 := by omega
      left
      simp only [flip, if_pos a]
      omega

private theorem descending_injection_fixed {α : Type} (T : α → α)
    (weight : α → Nat) (inj : ∀ {x y}, T x = T y → x = y)
    (fall : ∀ x, T x = x ∨ weight (T x) < weight x) (x : α) : T x = x := by
  suffices H : ∀ k y, weight y = k → T y = y from H _ x rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro y hy
    rcases fall y with h | h
    · exact h
    · exact inj (ih (weight (T y)) (by omega) (T y) rfl)

theorem tiling_eq_canonical {m n : Nat} {f : Board m n → Board m n}
    (hf : IsDiagonalTiling f) : f = canonical := by
  let T : Board m n → Board m n := fun x => canonical (f x)
  let weight : Board m n → Nat := fun x => score m x.1.val + score n x.2.val
  have inj : ∀ {x y}, T x = T y → x = y := by
    intro x y h
    have h' : f x = f y := by
      calc
        f x = canonical (T x) := (canonical_twice (f x)).symm
        _ = canonical (T y) := congrArg canonical h
        _ = f y := canonical_twice (f y)
    calc
      x = f (f x) := (hf.1 x).symm
      _ = f (f y) := congrArg f h'
      _ = y := hf.1 y
  have fall : ∀ x, T x = x ∨ weight (T x) < weight x := by
    intro x
    obtain ⟨hrow, hcol⟩ := hf.2 x
    have hr := coordinate_descent m _ _ (f x).1.isLt hrow
    have hc := coordinate_descent n _ _ (f x).2.isLt hcol
    change _ ∨ score m (flip (f x).1.val) + score n (flip (f x).2.val)
      < score m x.1.val + score n x.2.val
    rcases hr with er | lr <;> rcases hc with ec | lc
    · exact Or.inl (Prod.ext (Fin.ext er) (Fin.ext ec))
    · right; rw [er]; omega
    · right; rw [ec]; omega
    · right; omega
  funext x
  calc
    f x = canonical (T x) := (canonical_twice (f x)).symm
    _ = canonical x := congrArg canonical (descending_injection_fixed T weight inj fall x)

/-- Existence and uniqueness on every 2m by 2n board, quantified over all
partner functions satisfying the original adjacency and covering rules. -/
theorem exactly_one_diagonal_tiling (m n : Nat) :
    ∃ f : Board m n → Board m n,
      IsDiagonalTiling f ∧ ∀ g : Board m n → Board m n, IsDiagonalTiling g → g = f :=
  ⟨canonical, canonical_isTiling m n, fun _ hg => tiling_eq_canonical hg⟩

#print axioms exactly_one_diagonal_tiling

end DimerDiagonal
