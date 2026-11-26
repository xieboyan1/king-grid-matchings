import KingGrid.BoardEncoding
import KingGrid.StripPlacement

namespace BoardEncoding
open BoardCuts

def incidence (es : List Edge) (x y : Cell) : Prop :=
  (x,y) ∈ es ∨ (y,x) ∈ es

theorem incidence_symm {es : List Edge} {x y : Cell} :
    incidence es x y ↔ incidence es y x := or_comm

private theorem partner_of_incidence {m n : Nat} {es : List Edge}
    (T : Tiling m n es) {x y : Cell} (h : incidence es x y) : partner es x = y := by
  have hn := T.1.nodup_iff.mpr (boardNodup n m)
  rcases h with a|a
  · exact (partner_on_edge hn _ a).1
  · exact (partner_on_edge hn _ a).2

private theorem full_of_included {m n : Nat} {es ts : List Edge}
    (T : Tiling m n es) (U : Tiling m n ts)
    (incl : ∀ x y, incidence ts x y → incidence es x y) (x y : Cell) :
    incidence es x y ↔ incidence ts x y := by
  refine ⟨?_,incl x y⟩
  intro he
  have hx : x ∈ ends es := (ends_member _ _).2 (by
    rcases he with a|a
    · exact ⟨(x,y),a,Or.inl rfl⟩
    · exact ⟨(y,x),a,Or.inr rfl⟩)
  obtain ⟨e,hm,hm'⟩ := (ends_member ts x).1 (U.1.mem_iff.mpr (T.1.mem_iff.mp hx))
  obtain ⟨z,hz⟩ : ∃ z, incidence ts x z := by
    rcases hm' with a|a <;> subst x
    · exact ⟨_,Or.inl hm⟩
    · exact ⟨_,Or.inr hm⟩
  have eq : y=z := (partner_of_incidence T he).symm.trans
    (partner_of_incidence T (incl x z hz))
  exact eq ▸ hz

theorem encode_valid {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) :
    StripCounts.familyValid (2*m) (encode es m n) := by
  intro f hf
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
  exact ⟨_,matching T nv j (List.mem_range.mp hj)⟩

/-- Decoding the extracted row maps produces the original geometric edge
set, allowing edge-list reordering and independent reversal of endpoints. -/
theorem encode_decode_same {m n : Nat} {es : List Edge} (T : Tiling m n es)
    (nv : ∀ e ∈ es, e.1.2 ≠ e.2.2) (x y : Cell) :
    incidence es x y ↔ incidence (StripPlacement.edges m (encode es m n)) x y := by
  have hlen : (encode es m n).length = n := by simp [encode]
  have U := StripPlacement.edges_valid m _ (encode_valid T nv)
  rw [hlen] at U
  apply full_of_included T U
  intro u v
  have half {a b : Cell} (h : (a,b) ∈ StripPlacement.edges m (encode es m n)) :
      incidence es a b := by
    obtain ⟨j,hj,i,hi,hh⟩ := (StripPlacement.mem_from _ _ _ _).mp h
    have hrow : (encode es m n)[j] = rowMap es m (2*j) := by simp [encode]
    simp only [Nat.zero_add,hrow,Prod.mk.injEq] at hh
    rw [hh.1, hh.2]
    exact edge_from_left T nv j i (hlen ▸ hj) hi
  rintro (h|h)
  · exact half h
  · exact incidence_symm.mp (half h)

#print axioms encode_decode_same
end BoardEncoding
