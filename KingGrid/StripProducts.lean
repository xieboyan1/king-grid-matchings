import KingGrid.StripGeometry

/-!
# Counting actual matchings on a collection of adjacent column pairs

The j-th function takes the row i of a cell in column 2*j to the row f(i)
of its partner in column 2*j+1. Its inverse is specified existentially so
there is only one representation per matching. All functions are extended
by the identity outside the board. The membership and uniqueness theorems
quantify over arbitrary such functions, rather than only generated words.
-/

namespace StripCounts

abbrev RowMap := Nat → Nat
abbrev StripFamily := List RowMap

def totalFixed (h : Nat) : StripFamily → Nat
  | [] => 0
  | f :: fs => tally h (fun i => decide (f i = i)) + totalFixed h fs

def familyValid (h : Nat) (fs : StripFamily) : Prop :=
  ∀ f ∈ fs, ∃ g, StripMatching h f g

def realize (b : Board) : StripFamily := b.map action

theorem realize_valid {m : Nat} {b : Board} (hu : uniformHeight m b) :
    familyValid (2*m) (realize b) := by
  intro f hf
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hf
  exact ⟨action w, (hu w hw) ▸ word_is_matching w⟩

theorem realize_exact {m : Nat} {b : Board} (hu : uniformHeight m b) :
    totalFixed (2*m) (realize b) = totalSingles b := by
  induction b with
  | nil => rfl
  | cons w b ih =>
    have hw := hu w (by simp)
    have hb : uniformHeight m b := fun v hv => hu v (by simp [hv])
    change tally (2*m) _ + totalFixed (2*m) (realize b) = _
    rw [← hw, fixed_points_count, hw, ih hb]
    rfl

theorem realize_injective {m : Nat} {u v : Board} (hu : uniformHeight m u)
    (hv : uniformHeight m v) (he : realize u = realize v) : u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp [realize] at *
  | cons t u ih =>
    cases v with
    | nil => simp [realize] at he
    | cons s v =>
      obtain ⟨h₁,h₂⟩ := List.cons.inj he
      have hh₁ := hu t (by simp)
      have hh₂ := hv s (by simp)
      have ht := word_unique t s (hh₁.trans hh₂.symm) (fun i => congrFun h₁ i)
      have hp := ih (fun a ha => hu a (by simp [ha]))
        (fun a ha => hv a (by simp [ha])) h₂
      rw [ht,hp]

theorem realize_surjective (m : Nat) (fs : StripFamily) (hf : familyValid (2*m) fs) :
    ∃ b, uniformHeight m b ∧ realize b = fs := by
  induction fs with
  | nil => exact ⟨[], fun a ha => False.elim (by simp at ha), rfl⟩
  | cons f fs ih =>
    obtain ⟨g,hg⟩ := hf f (by simp)
    obtain ⟨w,hw,he⟩ := matching_has_word _ f g hg
    obtain ⟨b,hb,hr⟩ := ih (fun u hu => hf u (by simp [hu]))
    refine ⟨w :: b, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hw
      · exact hb v hv
    · change action w :: realize b = _
      rw [hr, ← funext he]

def horizontalMatchings (m n : Nat) : List StripFamily :=
  (twoBoards m n).map realize

theorem horizontal_membership (m n : Nat) (fs : StripFamily) :
    fs ∈ horizontalMatchings m n ↔
      fs.length = n ∧ familyValid (2*m) fs ∧ totalFixed (2*m) fs = 2 := by
  constructor
  · intro h
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    obtain ⟨hlen,hu,hs⟩ := (twoBoards_exact m n _).mp hb
    exact ⟨by simpa [realize] using hlen, realize_valid hu, (realize_exact hu).trans hs⟩
  · rintro ⟨hl,hf,hs⟩
    obtain ⟨b,hu,he⟩ := realize_surjective m fs hf
    apply List.mem_map.mpr
    refine ⟨b, (twoBoards_exact _ _ _).mpr ⟨?_,hu,?_⟩,he⟩
    · simpa [←he,realize] using hl
    · rw [← realize_exact hu, he]
      exact hs

private theorem nodup_image {α β : Type} (f : α → β) (xs : List α)
    (hn : xs.Nodup) (hi : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := List.mem_map.mp h
      exact ha ((hi y (by simp [hy]) a (by simp) he) ▸ hy)
    · exact ih hn (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))

theorem horizontal_nodup (m n : Nat) : (horizontalMatchings m n).Nodup := by
  apply nodup_image _ _ (twoBoards_nodup _ _)
  intro x hx y hy
  exact realize_injective ((twoBoards_exact _ _ _).mp hx).2.1
    ((twoBoards_exact _ _ _).mp hy).2.1

theorem horizontal_count (m n : Nat) :
    2*(horizontalMatchings m n).length = n*(m*(m+1)) := by
  simp only [horizontalMatchings, List.length_map, twoBoards_length]
  rw [Nat.mul_left_comm, twoSingle_count]

/-- A family of horizontal pairs and, on the transposed board, a family of
vertical pairs. The tags record the direction of the two straight dimers. -/
def orientedMatchings (m n : Nat) : List (Sum StripFamily StripFamily) :=
  (horizontalMatchings m n).map Sum.inl ++ (horizontalMatchings n m).map Sum.inr

theorem oriented_nodup (m n : Nat) : (orientedMatchings m n).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · exact nodup_image _ _ (horizontal_nodup _ _) (by intro _ _ _ _ he; simpa using he)
  · exact nodup_image _ _ (horizontal_nodup _ _) (by intro _ _ _ _ he; simpa using he)
  · intro x hx y hy
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hy
    simp

theorem oriented_count (m n : Nat) :
    2*(orientedMatchings m n).length = n*(m*(m+1)) + m*(n*(n+1)) := by
  simp only [orientedMatchings,List.length_append,List.length_map]
  rw [Nat.mul_add, horizontal_count, horizontal_count]

theorem oriented_square_count (n : Nat) :
    (orientedMatchings n n).length = n*n*(n+1) := by
  have h := oriented_count n n
  rw [Nat.mul_assoc]
  omega

#print axioms realize_surjective
#print axioms realize_injective
#print axioms horizontal_membership
#print axioms oriented_nodup
#print axioms oriented_square_count

end StripCounts
