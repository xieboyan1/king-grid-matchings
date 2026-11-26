import KingGrid.StripProducts
import KingGrid.BoardCells

namespace StripPlacement
open StripCounts BoardCuts

local instance : BEq Cell := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq Cell where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

def oneStrip (h j : Nat) (f : RowMap) : List Edge :=
  (List.range h).map (fun i => ((i,2*j),(f i,2*j+1)))

def fromStrip (h j : Nat) : StripFamily → List Edge
  | [] => []
  | f :: fs => oneStrip h j f ++ fromStrip h (j+1) fs

def edges (m : Nat) (fs : StripFamily) : List Edge := fromStrip (2*m) 0 fs

private theorem ends_append (a b : List Edge) : ends (a ++ b) = ends a ++ ends b := by
  induction a with
  | nil => rfl
  | cons e a ih => simp [ends, ih]

private theorem ends_split {α : Type} (a b : α → Cell) (xs : List α) :
    (ends (xs.map (fun i => (a i,b i)))).Perm (xs.map a ++ xs.map b) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.map_cons, ends, List.cons_append]
    apply List.Perm.cons
    exact (ih.cons (b x)).trans List.perm_middle.symm

private theorem wordPerm (w : Word) :
    ((List.range (height w)).map (action w)).Perm (List.range (height w)) := by
  induction w with
  | nil => exact .nil
  | cons t w ih =>
    cases t with
    | single =>
      simp only [height, List.range_succ_eq_map, List.map_cons, List.map_map, action]
      simpa only [List.map_map,Function.comp_def,action] using (ih.map (· + 1)).cons 0
    | cross =>
      simp only [height, List.range_succ_eq_map, List.map_cons, List.map_map, action]
      simpa only [List.map_map,Function.comp_def,action] using
        (((ih.map (· + 2)).cons 0).cons 1).trans (List.Perm.swap 0 1 _)

private theorem coord_count (h r c s : Nat) :
    ((List.range h).map (fun i => (i,c))).count (r,s) =
    if r < h ∧ c = s then 1 else 0 := by
  induction h with
  | zero => simp
  | succ h ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.count_append, ih, List.count_cons,List.count_nil,beq_iff_eq,
      Prod.mk.injEq,Nat.zero_add]
    split <;> split <;> split <;> omega

private theorem count_one (h j : Nat) (f : RowMap) (hf : ∃ g, StripMatching h f g)
    (r c : Nat) :
    (ends (oneStrip h j f)).count (r,c) =
    if r < h ∧ 2*j ≤ c ∧ c < 2*(j+1) then 1 else 0 := by
  obtain ⟨g,hg⟩ := hf
  obtain ⟨w,hw,he⟩ := matching_has_word h f g hg
  have p : ((List.range h).map f).Perm (List.range h) := by
    rw [funext he, ← hw]
    exact wordPerm w
  have pp := p.map (fun i => (i,2*j+1))
  have ppc := pp.count_eq (r,c)
  change _ = _ at ppc
  simp only [List.map_map, Function.comp_def] at ppc
  have hs := (ends_split (fun i => (i,2*j)) (fun i => (f i, 2*j+1))
    (List.range h)).count_eq (r,c)
  simp only [List.count_append, ppc,coord_count] at hs
  change (ends (oneStrip h j f)).count (r,c) = _ at hs
  rw [hs]
  split <;> split <;> split <;> omega

theorem cells_count (h j : Nat) (fs : StripFamily) (hf : familyValid h fs) (r c : Nat) :
    (ends (fromStrip h j fs)).count (r,c) =
    if r < h ∧ 2*j ≤ c ∧ c < 2*(j+fs.length) then 1 else 0 := by
  induction fs generalizing j with
  | nil => simp [fromStrip,ends]; split <;> omega
  | cons f fs ih =>
    have hf₁ := hf f (by simp)
    have hf₂ : familyValid h fs := fun a ha => hf a (by simp [ha])
    simp only [fromStrip,ends_append,List.count_append,count_one h j f hf₁ r c,
      ih (j+1) hf₂, List.length_cons]
    split <;> split <;> split <;> omega

theorem mem_from (h j : Nat) (fs : StripFamily) (e : Edge) :
    e ∈ fromStrip h j fs ↔ ∃ (k : Nat) (hk : k < fs.length) (i : Nat),
      i < h ∧ e = ((i,2*(j+k)),(fs[k] i,2*(j+k)+1)) := by
  induction fs generalizing j with
  | nil => simp [fromStrip]
  | cons f fs ih =>
    simp only [fromStrip,List.mem_append,oneStrip,List.mem_map,List.mem_range,
      List.length_cons, ih (j+1)]
    constructor
    · rintro (⟨i,hi,rfl⟩ | ⟨k,hk,i,hi,he⟩)
      · exact ⟨0,by omega,i,hi,by simp⟩
      · refine ⟨k+1,by omega,i,hi,?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    · rintro ⟨k,hk,i,hi,he⟩
      cases k with
      | zero => exact Or.inl ⟨i,hi, by simpa using he.symm⟩
      | succ k =>
        refine Or.inr ⟨k,by omega,i,hi,?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem no_vertical (m : Nat) (fs : StripFamily) : ∀ e ∈ edges m fs, e.1.2 ≠ e.2.2 := by
  intro e he
  obtain ⟨k,hk,i,hi,rfl⟩ := (mem_from _ _ _ _).mp he
  simp

theorem edges_valid (m : Nat) (fs : StripFamily) (hf : familyValid (2*m) fs) :
    Tiling m fs.length (edges m fs) := by
  constructor
  · apply List.perm_iff_count.mpr
    rintro ⟨r,c⟩
    simpa [edges, BoardCells.board_count] using cells_count (2*m) 0 fs hf r c
  · intro e he
    obtain ⟨k,hk,i,hi,rfl⟩ := (mem_from _ _ _ _).mp he
    obtain ⟨g,hg⟩ := hf fs[k] (List.getElem_mem hk)
    have hs := hg.step i
    refine ⟨?_, ?_, ?_⟩
    · simp
    · change Step i (fs[k] i)
      unfold Step
      omega
    · exact Or.inr (Or.inl rfl)

private theorem count_range (h : Nat) (p : Nat → Bool) :
    (List.range h).countP p = tally h p := by
  induction h generalizing p with
  | zero => rfl
  | succ h ih =>
    rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
    simp only [tally]
    rw [ih]
    rw [Nat.add_comm]
    rfl

private theorem count_fixed_from (h j : Nat) (fs : StripFamily) :
    (fromStrip h j fs).countP (flat Prod.fst) = totalFixed h fs := by
  induction fs generalizing j with
  | nil => rfl
  | cons f fs ih =>
    simp only [fromStrip,List.countP_append,oneStrip,List.countP_map,totalFixed,ih,count_range]
    congr 2
    funext i
    simp [flat,Function.comp_def,eq_comm]

theorem horizontal_count_edges (m : Nat) (fs : StripFamily) :
    (edges m fs).countP (flat Prod.fst) = totalFixed (2*m) fs := count_fixed_from _ _ _

theorem left_row_query (m : Nat) (fs : StripFamily) (k : Nat) (hk : k < fs.length)
    (i : Nat) (hi : i < 2*m) (s : Nat) :
    (((i,2*k),(s,2*k+1)) ∈ edges m fs ∨ ((s,2*k+1),(i,2*k)) ∈ edges m fs)
    ↔ s = fs[k] i := by
  constructor
  · rintro (he|he)
    · obtain ⟨j,hj,t,ht,hh⟩ := (mem_from _ _ _ _).mp he
      simp only [Nat.zero_add, Prod.mk.injEq] at hh
      obtain ⟨⟨rfl,hj'⟩,hs,_⟩ := hh
      have heq : k = j := by omega
      subst j
      exact hs
    · obtain ⟨j,hj,t,ht,hh⟩ := (mem_from _ _ _ _).mp he
      simp only [Nat.zero_add, Prod.mk.injEq] at hh
      omega
  · rintro rfl
    exact Or.inl ((mem_from _ _ _ _).2 ⟨k,hk,i,hi,by simp⟩)

theorem edges_faithful (m : Nat) (fs gs : StripFamily)
    (hf : familyValid (2*m) fs) (hg : familyValid (2*m) gs)
    (hl : fs.length = gs.length)
    (same : ∀ x y : Cell,
      ((x,y) ∈ edges m fs ∨ (y,x) ∈ edges m fs) ↔
      ((x,y) ∈ edges m gs ∨ (y,x) ∈ edges m gs)) : fs = gs := by
  apply List.ext_getElem hl
  intro k hk hk'
  funext i
  by_cases hi : i < 2*m
  · exact (left_row_query m gs k hk' i hi (fs[k] i)).mp
      ((same _ _).mp ((left_row_query m fs k hk i hi _).mpr rfl))
  · obtain ⟨f',h₁⟩ := hf fs[k] (List.getElem_mem hk)
    obtain ⟨g',h₂⟩ := hg gs[k] (List.getElem_mem hk')
    exact (h₁.outside i (by omega)).trans (h₂.outside i (by omega)).symm

#print axioms edges_valid
#print axioms horizontal_count_edges
#print axioms left_row_query
#print axioms edges_faithful

end StripPlacement
