import KingGrid.StripCounts

/-!
# Perfect matchings in two columns as words of singles and crosses

Index rows by natural numbers. A permutation sends each row in the left
column to its partner's row in the right column. Outside the strip it is
extended by the identity. Distances within the strip are at most one.
-/

namespace StripCounts

structure StripMatching (h : Nat) (f g : Nat → Nat) : Prop where
  back : ∀ i, g (f i) = i
  forth : ∀ i, f (g i) = i
  step : ∀ i, f i ≤ i+1 ∧ i ≤ f i+1
  outside : ∀ i, h ≤ i → f i = i

def action : Word → Nat → Nat
  | [], i => i
  | .single :: _, 0 => 0
  | .single :: w, i+1 => action w i + 1
  | .cross :: _, 0 => 1
  | .cross :: _, 1 => 0
  | .cross :: w, i+2 => action w i + 2

theorem word_is_matching (w : Word) :
    StripMatching (height w) (action w) (action w) := by
  induction w with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl, fun _ => by simp [action], fun _ _ => rfl⟩
  | cons t w ih =>
    cases t with
    | single =>
      constructor
      · intro i
        cases i <;> simp [action, ih.back]
      · intro i
        cases i <;> simp [action, ih.forth]
      · intro i
        cases i with
        | zero => simp [action]
        | succ i => have h := ih.step i; simp only [action]; omega
      · intro i hi
        cases i with
        | zero => rfl
        | succ i =>
          simp only [height] at hi
          simp [action, ih.outside i (by omega)]
    | cross =>
      constructor
      · intro i
        cases i with
        | zero => rfl
        | succ i => cases i <;> simp [action, ih.back]
      · intro i
        cases i with
        | zero => rfl
        | succ i => cases i <;> simp [action, ih.forth]
      · intro i
        cases i with
        | zero => simp [action]
        | succ i =>
          cases i with
          | zero => simp [action]
          | succ i => have h := ih.step i; simp only [action]; omega
      · intro i hi
        simp only [height] at hi
        cases i with
        | zero => omega
        | succ i =>
          cases i with
          | zero => omega
          | succ i => simp [action, ih.outside i (by omega)]

private def cut (p : Nat) (f : Nat → Nat) (i : Nat) := f (i+p)-p

private theorem cut_valid {h k p : Nat} {f g : Nat → Nat} (A : StripMatching h f g)
    (hlen : h = k+p) (hf : ∀ i, p ≤ i → p ≤ f i) (hg : ∀ i, p ≤ i → p ≤ g i) :
    StripMatching k (cut p f) (cut p g) := by
  constructor
  · intro i
    have ht := hf (i+p) (by omega)
    simp only [cut, Nat.sub_add_cancel ht, A.back, Nat.add_sub_cancel]
  · intro i
    have ht := hg (i+p) (by omega)
    simp only [cut, Nat.sub_add_cancel ht, A.forth, Nat.add_sub_cancel]
  · intro i
    have ht := A.step (i+p)
    simp only [cut]
    omega
  · intro i hi
    simp [cut, A.outside (i+p) (by omega)]

private theorem tail_stable {h p : Nat} {f g : Nat → Nat} (A : StripMatching h f g)
    (hf : ∀ i, i < p → f i < p) (hg : ∀ i, i < p → g i < p) :
    (∀ i, p ≤ i → p ≤ f i) ∧ (∀ i, p ≤ i → p ≤ g i) := by
  constructor
  · intro i hi
    by_cases hsmall : f i < p
    · have hback := hg (f i) hsmall
      rw [A.back] at hback
      omega
    · omega
  · intro i hi
    by_cases hsmall : g i < p
    · have hforth := hf (g i) hsmall
      rw [A.forth] at hforth
      omega
    · omega

theorem matching_has_word (h : Nat) (f g : Nat → Nat) (A : StripMatching h f g) :
    ∃ w : Word, height w = h ∧ ∀ i, f i = action w i := by
  induction h using Nat.strongRecOn generalizing f g with
  | ind h ih =>
    cases h with
    | zero => exact ⟨[], rfl, fun i => A.outside i (Nat.zero_le _)⟩
    | succ k =>
      have hs := A.step 0
      by_cases hz : f 0 = 0
      · have gz : g 0 = 0 := by simpa [hz] using A.back 0
        obtain ⟨hf,hg⟩ := tail_stable (p:=1) A
          (by
            intro i hi
            have he : i = 0 := by omega
            simp [he,hz])
          (by
            intro i hi
            have he : i = 0 := by omega
            simp [he,gz])
        obtain ⟨w, hw, he⟩ := ih k (by omega) _ _ (cut_valid A rfl hf hg)
        refine ⟨.single :: w, by simp [height,hw], ?_⟩
        intro i
        cases i with
        | zero => exact hz
        | succ i =>
          have eq := he i
          have lb := hf (i+1) (by omega)
          simp only [cut] at eq
          simp only [action]
          omega
      · have f0 : f 0 = 1 := by omega
        have g1 : g 1 = 0 := by simpa [f0] using A.back 0
        have fgi := A.forth 0
        have gin := A.step (g 0)
        have g0 : g 0 = 1 := by
          by_cases hz' : g 0 = 0
          · rw [hz'] at fgi
            omega
          · omega
        have f1 : f 1 = 0 := by simpa [g0] using fgi
        cases k with
        | zero => have := A.outside 1 (by decide); omega
        | succ k =>
          obtain ⟨hf,hg⟩ := tail_stable (p:=2) A
            (by intro i hi; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [f0,f1])
            (by intro i hi; rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [g0,g1])
          obtain ⟨w, hw, he⟩ := ih k (by omega) _ _ (cut_valid A rfl hf hg)
          refine ⟨.cross :: w, by simp [height,hw], ?_⟩
          intro i
          cases i with
          | zero => exact f0
          | succ i =>
            cases i with
            | zero => exact f1
            | succ i =>
              have eq := he i
              have lb := hf (i+2) (by omega)
              simp only [cut] at eq
              change f (i+2) = action w i + 2
              omega

theorem word_unique (u v : Word) (hh : height u = height v)
    (hf : ∀ i, action u i = action v i) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons t v => cases t <;> simp [height] at hh
  | cons t u ih =>
    cases v with
    | nil => cases t <;> simp [height] at hh
    | cons t' v =>
      have h0 := hf 0
      cases t <;> cases t' <;> simp only [action] at h0
      · have hw := ih v (by simp [height] at hh; exact hh)
          (fun i => by have eq := hf (i+1); simpa [action] using eq)
        rw [hw]
      · omega
      · omega
      · have hw := ih v (by simp [height] at hh; exact hh)
          (fun i => by have eq := hf (i+2); simpa [action] using eq)
        rw [hw]

def tally : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n+1, p => (if p 0 then 1 else 0) + tally n (fun i => p (i+1))

/-- A horizontal pair is exactly a left-row-to-right-row fixed point. -/
theorem fixed_points_count (w : Word) :
    tally (height w) (fun i => decide (action w i = i)) = singles w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    cases t <;> simp [height, action, tally, singles, ih] <;> omega

#print axioms word_is_matching
#print axioms matching_has_word
#print axioms word_unique
#print axioms fixed_points_count

end StripCounts
