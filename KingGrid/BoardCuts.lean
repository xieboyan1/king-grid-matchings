import Std

/- Rectangular king-graph matchings as lists of edges. Permutation of the
   endpoints with the list of board cells enforces exact coverage. -/
namespace BoardCuts

abbrev Cell := Nat × Nat
abbrev Edge := Cell × Cell

def block (i j : Nat) : List Cell :=
  [(2*i, 2*j), (2*i, 2*j+1), (2*i+1, 2*j), (2*i+1, 2*j+1)]

def band (i : Nat) : Nat → List Cell
  | 0 => []
  | n+1 => band i n ++ block i n

def board (n : Nat) : Nat → List Cell
  | 0 => []
  | m+1 => board n m ++ band m n

def ends : List Edge → List Cell
  | [] => []
  | e :: es => e.1 :: e.2 :: ends es

def Step (u v : Nat) : Prop := u = v ∨ u+1 = v ∨ v+1 = u

def Tiling (m n : Nat) (es : List Edge) : Prop :=
  (ends es).Perm (board n m) ∧
  ∀ e ∈ es, e.1 ≠ e.2 ∧ Step e.1.1 e.2.1 ∧ Step e.1.2 e.2.2

def mass {α : Type} (w : α → Int) : List α → Int
  | [] => 0
  | x :: xs => w x + mass w xs

theorem mass_append {α : Type} (w : α → Int) (xs ys : List α) :
    mass w (xs ++ ys) = mass w xs + mass w ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simp [mass, ih, Int.add_assoc]

theorem mass_perm {α : Type} (w : α → Int) {xs ys : List α} (h : xs.Perm ys) :
    mass w xs = mass w ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [mass, ih]
  | swap a b xs => simp only [mass]; omega
  | trans _ _ ih jh => exact ih.trans jh

theorem mass_board (w : Cell → Int) (z : ∀ i j, mass w (block i j) = 0) (m n : Nat) :
    mass w (board n m) = 0 := by
  have row : ∀ i k, mass w (band i k) = 0 := by
    intro i k
    induction k with
    | zero => rfl
    | succ k ih => simp [band, mass_append, ih, z]
  induction m with
  | zero => rfl
  | succ m ih => simp [board, mass_append, ih, row]

def sign (v : Nat) : Int := if v % 2 = 0 then 1 else -1
def flat (f : Cell → Nat) (e : Edge) : Bool := decide (f e.1 = f e.2)
def evenFlat (f : Cell → Nat) (e : Edge) : Bool :=
  decide (f e.1 = f e.2 ∧ f e.1 % 2 = 0)

theorem edge_sign (f : Cell → Nat) (e : Edge) (s : Step (f e.1) (f e.2)) :
    sign (f e.1) + sign (f e.2) =
    4 * (if evenFlat f e then (1:Int) else 0) -
    2 * (if flat f e then (1:Int) else 0) := by
  unfold sign evenFlat flat
  rcases s with h | h | h <;>
    by_cases a : f e.1 = f e.2 <;> by_cases b : f e.1 % 2 = 0 <;>
    by_cases c : f e.2 % 2 = 0 <;> simp [a,b,c] <;> omega

theorem count_sign (f : Cell → Nat) (es : List Edge)
    (s : ∀ e ∈ es, Step (f e.1) (f e.2)) :
    mass (fun x => sign (f x)) (ends es) =
    4 * (es.countP (evenFlat f) : Int) - 2 * (es.countP (flat f) : Int) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := edge_sign f e (s e (by simp))
    have ht := ih (fun a ha => s a (by simp [ha]))
    simp only [ends, mass, List.countP_cons]
    cases a : evenFlat f e <;> cases b : flat f e <;> simp [a,b] at he ⊢ <;> omega

theorem parallel_if_two (m n : Nat) (es : List Edge) (h : Tiling m n es)
    (two : es.countP (flat Prod.fst) + es.countP (flat Prod.snd) = 2) :
    es.countP (flat Prod.fst) = 0 ∨ es.countP (flat Prod.snd) = 0 := by
  obtain ⟨cov, legal⟩ := h
  have vr := count_sign Prod.fst es (fun e he => (legal e he).2.1)
  have vc := count_sign Prod.snd es (fun e he => (legal e he).2.2)
  have hr := mass_board (fun x => sign x.1) (by
    intro i j
    simp [block, mass, sign, Nat.add_mod]) m n
  have hc := mass_board (fun x => sign x.2) (by
    intro i j
    simp [block, mass, sign, Nat.add_mod]) m n
  rw [mass_perm _ cov, hr] at vr
  rw [mass_perm _ cov, hc] at vc
  omega

/- The alternating charge on the first 2k columns detects every edge
   crossing out of those columns with exactly the same sign. -/
def cut (k : Nat) (v : Cell) : Int := if v.2 < 2*k then sign v.2 else 0
def crosses (k : Nat) (e : Edge) : Bool :=
  decide ((e.1.2 < 2*k ∧ 2*k ≤ e.2.2) ∨ (e.2.2 < 2*k ∧ 2*k ≤ e.1.2))

theorem cut_block (k i j : Nat) : mass (cut k) (block i j) = 0 := by
  by_cases h : j < k
  · have u : 2*j < 2*k := by omega
    have v : 2*j+1 < 2*k := by omega
    simp [block, mass, cut, u, v, sign, Nat.add_mod]
  · have u : ¬ 2*j < 2*k := by omega
    have v : ¬ 2*j+1 < 2*k := by omega
    simp [block, mass, cut, u, v]

theorem cut_edge (k : Nat) (e : Edge) (s : e.1.2+1=e.2.2 ∨ e.2.2+1=e.1.2) :
    cut k e.1 + cut k e.2 = -(if crosses k e then (1:Int) else 0) := by
  unfold cut crosses sign
  rcases s with s | s <;>
    by_cases a : e.1.2 < 2*k <;> by_cases b : e.2.2 < 2*k <;>
    by_cases u : e.1.2 % 2 = 0 <;> by_cases v : e.2.2 % 2 = 0 <;>
    simp [a,b,u,v, Nat.le_of_not_gt] <;> omega

theorem cut_count (k : Nat) (es : List Edge)
    (s : ∀ e ∈ es, e.1.2+1=e.2.2 ∨ e.2.2+1=e.1.2) :
    mass (cut k) (ends es) = -(es.countP (crosses k) : Int) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := cut_edge k e (s e (by simp))
    have ht := ih (fun a ha => s a (by simp [ha]))
    simp only [ends, mass, List.countP_cons]
    cases a : crosses k e <;> simp [a] at he ⊢ <;> omega

theorem no_crossing_of_no_vertical (m n : Nat) (es : List Edge) (h : Tiling m n es)
    (noV : ∀ e ∈ es, e.1.2 ≠ e.2.2) (k : Nat) :
    es.countP (crosses k) = 0 := by
  obtain ⟨cov, legal⟩ := h
  have s : ∀ e ∈ es, e.1.2+1=e.2.2 ∨ e.2.2+1=e.1.2 := by
    intro e he
    exact ((legal e he).2.2).resolve_left (noV e he)
  have z := cut_count k es s
  rw [mass_perm _ cov, mass_board (cut k) (cut_block k)] at z
  omega

theorem same_column_pair (m n : Nat) (es : List Edge) (h : Tiling m n es)
    (noV : ∀ e ∈ es, e.1.2 ≠ e.2.2) : ∀ e ∈ es, e.1.2 / 2 = e.2.2 / 2 := by
  intro e he
  have cutfree (k : Nat) := List.countP_eq_zero.mp (no_crossing_of_no_vertical m n es h noV k) e he
  have l := cutfree (e.1.2/2 + 1)
  have r := cutfree (e.2.2/2 + 1)
  simp [crosses] at l r
  omega

#print axioms parallel_if_two
#print axioms same_column_pair
end BoardCuts
