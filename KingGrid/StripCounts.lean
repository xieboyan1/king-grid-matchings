import Std

/-!
# Counting an even rectangular board after splitting it into two-column strips

A single tile occupies one row and joins the two cells horizontally. A cross
occupies two rows and pairs their four cells by the two diagonals. A board in
this file is a list of such strips. The relation to the two-dimensional king
graph is a separate question from the counting proved here.
-/

namespace StripCounts

inductive Tile where
  | single
  | cross
  deriving DecidableEq, Repr

abbrev Word := List Tile
abbrev Board := List Word

def singles : Word → Nat
  | [] => 0
  | .single :: w => singles w + 1
  | .cross :: w => singles w

def height : Word → Nat
  | [] => 0
  | .single :: w => height w + 1
  | .cross :: w => height w + 2

theorem height_count (w : Word) : height w + singles w = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    cases t <;> simp only [height, singles, List.length_cons] <;> omega

/-- Enumerate exactly the words with l tiles, of which s are singles. -/
def words : Nat → Nat → List Word
  | 0, 0 => [[]]
  | 0, _+1 => []
  | l+1, 0 => (words l 0).map (Tile.cross :: ·)
  | l+1, s+1 =>
    (words l s).map (Tile.single :: ·) ++
    (words l (s+1)).map (Tile.cross :: ·)

theorem mem_words (l s : Nat) (w : Word) :
    w ∈ words l s ↔ w.length = l ∧ singles w = s := by
  induction l generalizing s w with
  | zero =>
    cases s <;> cases w <;> simp [words, singles]
  | succ l ih =>
    cases s <;> cases w with
    | nil => simp [words]
    | cons t w =>
      cases t <;> simp [words, singles, ih, List.mem_map]

private theorem nodupMapInj {α β : Type} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (xs : List α) (h : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨z, hz, he⟩ := List.mem_map.mp hm
      exact hx (hf z x he ▸ hz)
    · exact ih ht

private theorem nodupAdd {α : Type} (xs ys : List α)
    (hx : xs.Nodup) (hy : ys.Nodup)
    (dis : ∀ a, a ∈ xs → a ∈ ys → False) : (xs ++ ys).Nodup := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    obtain ⟨hna, hn⟩ := List.nodup_cons.mp hx
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hna hm
      · exact dis x (by simp) hm
    · exact ih hn (fun a ha => dis a (by simp [ha]))

theorem words_nodup (l s : Nat) : (words l s).Nodup := by
  induction l generalizing s with
  | zero => cases s <;> simp [words]
  | succ l ih =>
    cases s with
    | zero => exact nodupMapInj _ (by intro a b e; simpa using e) _ (ih 0)
    | succ s =>
      apply nodupAdd
      · apply nodupMapInj _ (by intro a b e; simpa using e) _ (ih s)
      · apply nodupMapInj _ (by intro a b e; simpa using e) _ (ih (s+1))
      · intro w h₁ h₂
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp h₁
        simp at h₂

def zeroStrip (m : Nat) : Word := List.replicate m .cross

@[simp] theorem zeroStrip_height (m : Nat) : height (zeroStrip m) = 2*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [zeroStrip, List.replicate_succ, height] at * <;> omega

@[simp] theorem zeroStrip_singles (m : Nat) : singles (zeroStrip m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [zeroStrip, List.replicate_succ, singles] using ih

theorem zeroStrip_unique {w : Word} (h : singles w = 0) :
    w = zeroStrip w.length := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    cases t with
    | single => simp [singles] at h
    | cross => simpa [zeroStrip, List.replicate_succ] using ih h

def totalSingles : Board → Nat
  | [] => 0
  | w :: b => singles w + totalSingles b

def uniformHeight (m : Nat) (b : Board) := ∀ w ∈ b, height w = 2*m

private theorem uniform_cons (m : Nat) (w : Word) (b : Board) :
    uniformHeight m (w :: b) ↔ height w = 2*m ∧ uniformHeight m b := by
  constructor
  · intro h
    exact ⟨h w (by simp), fun v hv => h v (by simp [hv])⟩
  · rintro ⟨hw,hb⟩ v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw
    · exact hb v hv

def zeroBoard (m n : Nat) : Board := List.replicate n (zeroStrip m)

theorem zeroBoard_exact (m n : Nat) (b : Board) :
    b = zeroBoard m n ↔ b.length = n ∧ uniformHeight m b ∧ totalSingles b = 0 := by
  induction n generalizing b with
  | zero => cases b <;> simp [zeroBoard, uniformHeight, totalSingles]
  | succ n ih =>
    cases b with
    | nil => simp [zeroBoard, List.replicate_succ]
    | cons w b =>
      simp only [zeroBoard, List.replicate_succ, List.cons.injEq, List.length_cons,
        Nat.succ.injEq, uniform_cons, totalSingles]
      change (w = zeroStrip m ∧ b = zeroBoard m n) ↔ _
      rw [ih]
      constructor
      · rintro ⟨rfl, hb, hu, ht⟩
        simp [hb, hu, ht]
      · rintro ⟨hb, ⟨hw, hu⟩, ht⟩
        have hs : singles w = 0 := by omega
        have hl := height_count w
        have he : w.length = m := by omega
        exact ⟨(zeroStrip_unique hs).trans (by rw [he]), hb, hu, by omega⟩

/-- Enumerate boards carrying precisely two singles, all strips of height twice m. -/
def twoBoards (m : Nat) : Nat → List Board
  | 0 => []
  | n+1 => (words (m+1) 2).map (fun w => w :: zeroBoard m n) ++
      (twoBoards m n).map (zeroStrip m :: ·)

theorem twoBoards_exact (m n : Nat) (b : Board) :
    b ∈ twoBoards m n ↔ b.length = n ∧ uniformHeight m b ∧ totalSingles b = 2 := by
  induction n generalizing b with
  | zero => cases b <;> simp [twoBoards, totalSingles]
  | succ n ih =>
    cases b with
    | nil => simp [twoBoards]
    | cons w b =>
      simp only [twoBoards, List.mem_append, List.mem_map, List.cons.injEq,
        List.length_cons, Nat.succ.injEq, uniform_cons, totalSingles]
      constructor
      · rintro (⟨v,hv,rfl,rfl⟩ | ⟨t,ht,rfl,rfl⟩)
        · obtain ⟨hl,hs⟩ := (mem_words _ _ _).mp hv
          obtain ⟨hb,hu,hz⟩ := (zeroBoard_exact m n _).mp rfl
          have hh := height_count v
          exact ⟨hb, ⟨by omega, hu⟩, by omega⟩
        · obtain ⟨hb,hu,hs⟩ := (ih _).mp ht
          exact ⟨hb, ⟨zeroStrip_height _, hu⟩, by simp [hs]⟩
      · rintro ⟨hb, ⟨hw, hu⟩, ht⟩
        have hh := height_count w
        by_cases hz : singles w = 0
        · have hl : w.length = m := by omega
          have he : w = zeroStrip m := (zeroStrip_unique hz).trans (by rw [hl])
          exact Or.inr ⟨b, (ih b).mpr ⟨hb, hu, by omega⟩, he.symm, rfl⟩
        · have hs : singles w = 2 := by omega
          have hl : w.length = m+1 := by omega
          exact Or.inl ⟨w, (mem_words _ _ _).mpr ⟨hl,hs⟩, rfl,
            ((zeroBoard_exact m n b).mpr ⟨hb,hu,by omega⟩).symm⟩

theorem twoBoards_nodup (m n : Nat) : (twoBoards m n).Nodup := by
  induction n with
  | zero => simp [twoBoards]
  | succ n ih =>
    apply nodupAdd
    · apply nodupMapInj _ (by intro a b e; simpa using e) _ (words_nodup _ _)
    · apply nodupMapInj _ (by intro a b e; simpa using e) _ ih
    · intro b h₁ h₂
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h₁
      obtain ⟨z,_,he⟩ := List.mem_map.mp h₂
      have he' : zeroStrip m = v := (List.cons.inj he).1
      have hs := ((mem_words _ _ _).mp hv).2
      simp [← he'] at hs

private theorem noSingle_count (n : Nat) : (words n 0).length = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [words] using ih

private theorem oneSingle_count (n : Nat) : (words n 1).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [words, noSingle_count, ih, Nat.add_comm]

/-- The binomial coefficient (m+1 choose 2), written without division. -/
theorem twoSingle_count (m : Nat) :
    2 * (words (m+1) 2).length = m*(m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    change 2 * ((words (m+1) 1).map _ ++ (words (m+1) 2).map _).length = _
    simp only [List.length_append, List.length_map, oneSingle_count, Nat.mul_add]
    rw [ih]
    simp only [Nat.succ_mul, Nat.mul_succ, Nat.mul_one]
    omega

theorem twoBoards_length (m n : Nat) :
    (twoBoards m n).length = n * (words (m+1) 2).length := by
  induction n with
  | zero => simp [twoBoards]
  | succ n ih =>
    simp only [twoBoards, List.length_append, List.length_map, ih, Nat.succ_mul]
    omega

/-- Horizontal and vertical cases are distinguished by their orientation. -/
def bothDirections (m n : Nat) : List (Sum Board Board) :=
  (twoBoards m n).map Sum.inl ++ (twoBoards n m).map Sum.inr

theorem bothDirections_nodup (m n : Nat) : (bothDirections m n).Nodup := by
  apply nodupAdd
  · apply nodupMapInj _ (by intro a b e; simpa using e) _ (twoBoards_nodup _ _)
  · apply nodupMapInj _ (by intro a b e; simpa using e) _ (twoBoards_nodup _ _)
  · intro a h₁ h₂
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp h₁
    simp at h₂

theorem rectangle_count (m n : Nat) :
    2 * (bothDirections m n).length = n*(m*(m+1)) + m*(n*(n+1)) := by
  simp only [bothDirections, List.length_append, List.length_map, twoBoards_length]
  rw [Nat.mul_add]
  calc
    _ = n*(2*(words (m+1) 2).length) + m*(2*(words (n+1) 2).length) := by
      simp only [Nat.mul_left_comm]
    _ = _ := by rw [twoSingle_count, twoSingle_count]

theorem square_count (n : Nat) : (bothDirections n n).length = n*n*(n+1) := by
  have h := rectangle_count n n
  rw [Nat.mul_assoc]
  omega

#print axioms twoBoards_exact
#print axioms bothDirections_nodup
#print axioms rectangle_count
#print axioms square_count

end StripCounts
