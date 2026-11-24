import Mathlib
import PEqualNP.Defs

open scoped BigOperators Sym2

namespace PEqualNP.Outside.L_meta_2693_aux

abbrev G : SimpleGraph (Fin 11) :=
  PEqualNP.EdgeOwnership.edgeGraph 11
    [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
     (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

-- Count each selected vertex twice around its own odd cycle. The three
-- disjoint cycles require at least two, two, and three vertices respectively.
theorem coverFloor (S : Finset (Fin 11)) (covers : G.IsVertexCover ↑S) : 7 ≤ S.card := by
  let selected (u : Fin 11) : ℕ := if u ∈ S then 1 else 0
  have paid {u v : Fin 11} (h : G.Adj u v) : 1 ≤ selected u + selected v := by
    rcases covers h with hu | hv
    · have mem : u ∈ S := hu
      simp [selected,mem]
    · have mem : v ∈ S := hv
      simp [selected,mem]
  have p14 := paid (u := 1) (v := 4) (by decide)
  have p18 := paid (u := 1) (v := 8) (by decide)
  have p48 := paid (u := 4) (v := 8) (by decide)
  have p36 := paid (u := 3) (v := 6) (by decide)
  have p37 := paid (u := 3) (v := 7) (by decide)
  have p67 := paid (u := 6) (v := 7) (by decide)
  have p09 := paid (u := 0) (v := 9) (by decide)
  have p0a := paid (u := 0) (v := 10) (by decide)
  have p25 := paid (u := 2) (v := 5) (by decide)
  have p2a := paid (u := 2) (v := 10) (by decide)
  have p59 := paid (u := 5) (v := 9) (by decide)
  have triangle1 : 2 ≤ selected 1 + selected 4 + selected 8 := by omega
  have triangle2 : 2 ≤ selected 3 + selected 6 + selected 7 := by omega
  have pentagon : 3 ≤ selected 0 + selected 2 + selected 5 + selected 9 + selected 10 := by omega
  have card : S.card = ∑ u : Fin 11, selected u :=
    Finset.card_eq_sum_ite (Finset.subset_univ S)
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at card
  change S.card = selected 0 + (selected 1 + (selected 2 + (selected 3 + (selected 4 +
    (selected 5 + (selected 6 + (selected 7 + (selected 8 + (selected 9 + (selected 10 + 0)))))))))) at card
  omega

-- Restore one arbitrarily chosen endpoint per deleted edge. Repeated choices
-- can only make the extended cover smaller.
theorem restore {V : Type} [DecidableEq V] (G : SimpleGraph V) (removed : Finset (Sym2 V))
    (S : Finset V) (cover : (G.deleteEdges ↑removed).IsVertexCover ↑S) :
    ∃ T : Finset V, G.IsVertexCover ↑T ∧ T.card ≤ S.card+removed.card := by
  classical
  have hasEndpoint (e : Sym2 V) : ∃ v, v ∈ e :=
    e.inductionOn (fun u v => ⟨u,by simp⟩)
  let pick (e : Sym2 V) := Classical.choose (hasEndpoint e)
  let ends := removed.image pick
  refine ⟨S ∪ ends,?_,(Finset.card_union_le S ends).trans ?_⟩
  · intro u v edge
    by_cases lost : s(u,v) ∈ removed
    · have inEnds : pick (s(u,v)) ∈ ends := Finset.mem_image.mpr ⟨_,lost,rfl⟩
      have incident : pick (s(u,v)) = u ∨ pick (s(u,v)) = v :=
        Sym2.mem_iff.mp (Classical.choose_spec (hasEndpoint (s(u,v))))
      rcases incident with h | h
      · exact Or.inl (Finset.mem_union_right _ (h ▸ inEnds))
      · exact Or.inr (Finset.mem_union_right _ (h ▸ inEnds))
    · obtain hu | hv := cover (SimpleGraph.deleteEdges_adj.mpr ⟨edge,lost⟩)
      · exact Or.inl (Finset.mem_union_left _ hu)
      · exact Or.inr (Finset.mem_union_left _ hv)
  · exact Nat.add_le_add_left Finset.card_image_le _

end PEqualNP.Outside.L_meta_2693_aux

theorem PEqualNP.Outside.L_meta_2693 :
    have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
      [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
       ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
       ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
       ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
    ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))),
      (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  dsimp only
  intro removed S cover
  obtain ⟨T,good,card⟩ := L_meta_2693_aux.restore L_meta_2693_aux.G removed S cover
  exact (L_meta_2693_aux.coverFloor T good).trans card
