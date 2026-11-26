import KingGrid.BoardCuts
import KingGrid.StripProducts

namespace BoardEncoding
open BoardCuts

private theorem memberBlock (r c i j : Nat) :
    (r,c) ∈ block i j ↔ r/2 = i ∧ c/2 = j := by
  simp [block, Prod.ext_iff]
  omega

private theorem memberBand (r c i n : Nat) :
    (r,c) ∈ band i n ↔ r/2 = i ∧ c < 2*n := by
  induction n with
  | zero => simp [band]
  | succ n ih => simp only [band, List.mem_append, ih, memberBlock]; omega

theorem memberBoard (r c n m : Nat) :
    (r,c) ∈ board n m ↔ r < 2*m ∧ c < 2*n := by
  induction m with
  | zero => simp [board]
  | succ m ih => simp only [board, List.mem_append, ih, memberBand]; omega

private theorem appendNodup {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ p ∈ xs, p ∈ ys → False) :
    (xs ++ ys).Nodup := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hx
    apply List.nodup_cons.mpr
    constructor
    · intro p
      rcases List.mem_append.mp p with p|p
      · exact hn p
      · exact hd x (by simp) p
    · exact ih ht (fun p hp => hd p (by simp [hp]))

private theorem blockNodup (i j : Nat) : (block i j).Nodup := by
  simp [block, Prod.ext_iff]

private theorem bandNodup (i n : Nat) : (band i n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    apply appendNodup ih (blockNodup i n)
    rintro ⟨r,c⟩ hp hq
    rw [memberBand] at hp
    rw [memberBlock] at hq
    omega

theorem boardNodup (n m : Nat) : (board n m).Nodup := by
  induction m with
  | zero => exact List.nodup_nil
  | succ m ih =>
    apply appendNodup ih (bandNodup m n)
    rintro ⟨r,c⟩ hp hq
    rw [memberBoard] at hp
    rw [memberBand] at hq
    omega

/-- Read the other endpoint of the unique incident edge. Off the board
the default value is the input cell. -/
def partner : List Edge → Cell → Cell
  | [], x => x
  | e::es, x => if x=e.1 then e.2 else if x=e.2 then e.1 else partner es x

theorem ends_member (es : List Edge) (x : Cell) :
    x ∈ ends es ↔ ∃ e ∈ es, x=e.1 ∨ x=e.2 := by
  induction es with
  | nil => simp [ends]
  | cons e es ih =>
    simp only [ends, List.mem_cons, ih]
    constructor
    · rintro (h|h|h)
      · exact ⟨e, Or.inl rfl, Or.inl h⟩
      · exact ⟨e, Or.inl rfl, Or.inr h⟩
      · obtain ⟨u, hu, he⟩ := h
        exact ⟨u, Or.inr hu, he⟩
    · rintro ⟨u, rfl|hu, he⟩
      · exact he.elim Or.inl (Or.inr ∘ Or.inl)
      · exact Or.inr (Or.inr ⟨u,hu,he⟩)

theorem partner_on_edge {es : List Edge} (hn : (ends es).Nodup)
    (e : Edge) (he : e ∈ es) : partner es e.1 = e.2 ∧ partner es e.2 = e.1 := by
  induction es with
  | nil => simp at he
  | cons u es ih =>
    obtain ⟨hu1, ht⟩ := List.nodup_cons.mp hn
    obtain ⟨hu2, ht'⟩ := List.nodup_cons.mp ht
    rcases List.mem_cons.mp he with rfl | he
    · have hne : e.2 ≠ e.1 := fun h => hu1 (by simp [h])
      simp [partner, hne]
    · have h1 := (ends_member es e.1).2 ⟨e,he,Or.inl rfl⟩
      have h2 := (ends_member es e.2).2 ⟨e,he,Or.inr rfl⟩
      have h11 : e.1 ≠ u.1 := fun h => hu1 (List.mem_cons_of_mem _ (h ▸ h1))
      have h12 : e.1 ≠ u.2 := fun h => hu2 (h ▸ h1)
      have h21 : e.2 ≠ u.1 := fun h => hu1 (List.mem_cons_of_mem _ (h ▸ h2))
      have h22 : e.2 ≠ u.2 := fun h => hu2 (h ▸ h2)
      simpa [partner,h11,h12,h21,h22] using ih ht' he

private theorem stepSymm {x y : Nat} (h : Step x y) : Step y x := by
  unfold Step at *
  omega

theorem partner_spec {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2)
    (r c : Nat) (hr : r < 2*m) (hc : c < 2*n) :
    let y := partner es (r,c)
    y.1 < 2*m ∧ y.2 < 2*n ∧ y.2/2 = c/2 ∧ y.2 ≠ c ∧ Step r y.1 ∧
      partner es y = (r,c) ∧ (((r,c),y) ∈ es ∨ (y,(r,c)) ∈ es) := by
  have hin := T.1.mem_iff.mpr ((memberBoard r c n m).mpr ⟨hr,hc⟩)
  obtain ⟨e,he,hp⟩ := (ends_member es _).mp hin
  have hu := (ends_member es e.1).2 ⟨e,he,Or.inl rfl⟩
  have hv := (ends_member es e.2).2 ⟨e,he,Or.inr rfl⟩
  have bu := (memberBoard e.1.1 e.1.2 n m).mp (T.1.mem_iff.mp hu)
  have bv := (memberBoard e.2.1 e.2.2 n m).mp (T.1.mem_iff.mp hv)
  have eqs := partner_on_edge (T.1.nodup_iff.mpr (boardNodup n m)) e he
  have bs := same_column_pair m n es T nv e he
  have rs := (T.2 e he).2.1
  dsimp only
  rcases hp with h|h
  · rw [h,eqs.1]
    have eqr := congrArg Prod.fst h
    have eqc := congrArg Prod.snd h
    change r = _ at eqr
    change c = _ at eqc
    rw [eqr,eqc]
    exact ⟨bv.1,bv.2,bs.symm,Ne.symm (nv e he),rs,eqs.2,Or.inl he⟩
  · rw [h,eqs.2]
    have eqr := congrArg Prod.fst h
    have eqc := congrArg Prod.snd h
    change r = _ at eqr
    change c = _ at eqc
    rw [eqr,eqc]
    exact ⟨bu.1,bu.2,bs,nv e he,stepSymm rs,eqs.1,Or.inr he⟩

/-- The right partner row of a left cell, padded outside the height. -/
def rowMap (es : List Edge) (m c i : Nat) :=
  if i < 2*m then (partner es (i,c)).1 else i

theorem matching {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) (j : Nat) (hj : j < n) :
    StripCounts.StripMatching (2*m) (rowMap es m (2*j)) (rowMap es m (2*j+1)) := by
  have rule (c d i : Nat) (hi : i < 2*m) (h : c < 2*n)
      (hp : ∀ v : Nat, v/2=c/2 → v ≠ c → v=d) :
      rowMap es m d (rowMap es m c i) = i := by
    obtain ⟨hb,_,he,hn,_,hh,_⟩ := partner_spec T nv i c hi h
    have hd := hp _ he hn
    have hv : ((partner es (i,c)).1,d) = partner es (i,c) := Prod.ext rfl hd.symm
    simpa [rowMap,hi,hb,hv] using congrArg Prod.fst hh
  constructor
  · intro i
    by_cases hi : i < 2*m
    · exact rule _ _ _ hi (by omega) (by omega)
    · simp [rowMap,hi]
  · intro i
    by_cases hi : i < 2*m
    · exact rule _ _ _ hi (by omega) (by omega)
    · simp [rowMap,hi]
  · intro i
    by_cases hi : i < 2*m
    · have hh := (partner_spec T nv i (2*j) hi (by omega)).2.2.2.2.1
      simp only [rowMap, if_pos hi]
      unfold Step at hh
      omega
    · simp [rowMap,hi]
  · intro i hi
    simp [rowMap, Nat.not_lt.mpr hi]

theorem edge_from_left {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) (j i : Nat) (hj : j < n) (hi : i < 2*m) :
    let e : Edge := ((i,2*j),(rowMap es m (2*j) i,2*j+1))
    e ∈ es ∨ (e.2,e.1) ∈ es := by
  obtain ⟨_,_,he,hn,_,_,hh⟩ := partner_spec T nv i (2*j) hi (by omega)
  dsimp only
  have hd : (partner es (i,2*j)).2 = 2*j+1 := by omega
  have hv : (rowMap es m (2*j) i,2*j+1) = partner es (i,2*j) := by
    apply Prod.ext
    · simp [rowMap,hi]
    · exact hd.symm
  rw [hv]
  exact hh

#print axioms matching
#print axioms edge_from_left

/-- The tuple of strip permutations read geometrically from the edge list. -/
def encode (es : List Edge) (m n : Nat) : StripCounts.StripFamily :=
  (List.range n).map (fun j => rowMap es m (2*j))

private def sigma : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k+1, f => sigma k f + f k

private theorem sigma_add (k : Nat) (f g : Nat → Nat) :
    sigma k (fun i => f i + g i) = sigma k f + sigma k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sigma,ih]; omega

private theorem tally_last (k : Nat) (p : Nat → Bool) :
    StripCounts.tally (k+1) p = StripCounts.tally k p + (if p k then 1 else 0) := by
  induction k generalizing p with
  | zero => simp [StripCounts.tally]
  | succ k ih =>
    change (if p 0 then 1 else 0) + StripCounts.tally (k+1) (fun i => p (i+1)) =
      ((if p 0 then 1 else 0) + StripCounts.tally k (fun i => p (i+1))) +
      (if p (k+1) then 1 else 0)
    rw [ih]
    omega

private def charge (p : Nat → Nat → Bool) (x : Cell) : Int :=
  if x.2%2=0 ∧ p x.1 (x.2/2) = true then 1 else 0

private def bit (b : Bool) : Nat := if b then 1 else 0

private theorem band_charge (p : Nat → Nat → Bool) (i n : Nat) :
    mass (charge p) (band i n) =
      (sigma n (fun j => bit (p (2*i) j) + bit (p (2*i+1) j)) : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have q : (2*n)/2=n := by omega
    have e : (2*n)%2=0 := by omega
    have o : (2*n+1)%2≠0 := by omega
    simp only [band,mass_append,ih,sigma,block,mass,charge,bit,e,o,q,
      true_and, false_and, if_false, Int.add_zero, Int.ofNat_add]
    cases p (2*i) n <;> cases p (2*i+1) n <;> simp

private theorem board_charge (p : Nat → Nat → Bool) (m n : Nat) :
    mass (charge p) (board n m) =
      (sigma n (fun j => StripCounts.tally (2*m) (fun i => p i j)) : Int) := by
  induction m with
  | zero =>
    change 0 = (sigma n (fun _ => 0) : Int)
    induction n with
    | zero => rfl
    | succ n ih => simpa [sigma] using ih
  | succ m ih =>
    have he : 2*(m+1)=(2*m+1)+1 := by omega
    have hf : (fun j => StripCounts.tally (2*(m+1)) (fun i => p i j)) =
      fun j => StripCounts.tally (2*m) (fun i => p i j) +
        (bit (p (2*m) j) + bit (p (2*m+1) j)) := by
      funext j
      rw [he,tally_last,tally_last]
      simp [bit,Nat.add_assoc]
    rw [board,mass_append,ih,band_charge,hf]
    simp only [sigma_add, Int.ofNat_add]

private theorem per_edge {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) {e : Edge} (he : e ∈ es) :
    let p := fun i j => decide (rowMap es m (2*j) i = i)
    charge p e.1 + charge p e.2 = (if flat Prod.fst e then 1 else 0) := by
  have hn := T.1.nodup_iff.mpr (boardNodup n m)
  obtain ⟨u,v⟩ := partner_on_edge hn e he
  have bu := (memberBoard e.1.1 e.1.2 n m).mp (T.1.mem_iff.mp
    ((ends_member es _).mpr ⟨e,he,Or.inl rfl⟩))
  have bv := (memberBoard e.2.1 e.2.2 n m).mp (T.1.mem_iff.mp
    ((ends_member es _).mpr ⟨e,he,Or.inr rfl⟩))
  have orth := ((T.2 e he).2.2).resolve_left (nv e he)
  dsimp only
  by_cases hc : e.1.2%2=0
  · have co : e.2.2%2≠0 := by omega
    have ee : 2*(e.1.2/2)=e.1.2 := by omega
    simp [charge,hc,co,ee,rowMap,bu.1,u,flat,eq_comm]
  · have co : e.2.2%2=0 := by omega
    have ee : 2*(e.2.2/2)=e.2.2 := by omega
    simp [charge,hc,co,ee,rowMap,bv.1,v,flat]

private theorem endpoints_charge {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) :
    mass (charge (fun i j => decide (rowMap es m (2*j) i = i))) (ends es) =
      (es.countP (flat Prod.fst) : Int) := by
  suffices all : ∀ ks : List Edge, (∀ e ∈ ks, e ∈ es) →
    mass (charge (fun i j => decide (rowMap es m (2*j) i = i))) (ends ks) =
      (ks.countP (flat Prod.fst) : Int) from all es (fun _ he => he)
  intro ks
  induction ks with
  | nil => intro _; rfl
  | cons e ks ih =>
    intro incl
    have ee := per_edge T nv (incl e (by simp))
    have et := ih (fun u hu => incl u (by simp [hu]))
    simp only [ends,mass,List.countP_cons,et]
    cases e0 : flat Prod.fst e <;> simp [e0] at ee ⊢ <;> omega

private theorem appendFixed (h : Nat) (u v : StripCounts.StripFamily) :
    StripCounts.totalFixed h (u++v) = StripCounts.totalFixed h u + StripCounts.totalFixed h v := by
  induction u with
  | nil => simp [StripCounts.totalFixed]
  | cons f fs ih => simp [StripCounts.totalFixed,ih,Nat.add_assoc]

private theorem total_as_sum (es : List Edge) (m n : Nat) :
    StripCounts.totalFixed (2*m) (encode es m n) =
      sigma n (fun j => StripCounts.tally (2*m) (fun i => decide (rowMap es m (2*j) i = i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold encode at *
    rw [List.range_succ,List.map_append,appendFixed,ih]
    simp [sigma,StripCounts.totalFixed]

theorem encode_count {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) :
    StripCounts.totalFixed (2*m) (encode es m n) = es.countP (flat Prod.fst) := by
  have h := endpoints_charge T nv
  rw [mass_perm _ T.1, board_charge] at h
  rw [total_as_sum]
  exact Int.ofNat_inj.mp h

theorem encode_horizontal {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) (two : es.countP (flat Prod.fst) = 2) :
    encode es m n ∈ StripCounts.horizontalMatchings m n := by
  apply (StripCounts.horizontal_membership _ _ _).mpr
  refine ⟨by simp [encode], ?_, (encode_count T nv).trans two⟩
  intro f hf
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
  exact ⟨_,matching T nv j (List.mem_range.mp hj)⟩

#print axioms encode_count
#print axioms encode_horizontal
end BoardEncoding
