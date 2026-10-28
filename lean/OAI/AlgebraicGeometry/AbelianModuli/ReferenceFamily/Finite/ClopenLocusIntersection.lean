import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClopenLocusGluing

/-! # Clopen Locus Intersection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ClopenLocusIntersection

noncomputable section

/-! Finitely many clopen scheme loci have their actual clopen
intersection, with the unique lifting property on arbitrary tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem finiteClopenLocusIntersection {S : Scheme.{0}} {I : Type} [Finite I]
    (L : I → S.Opens) (hL : ∀ i, IsClosed (L i : Set S)) :
    ∃ U : S.Opens, IsClosed (U : Set S) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S),
        (∀ i, ∃! f : T ⟶ (L i).toScheme, f ≫ (L i).ι = x) ↔
          ∃! f : T ⟶ U.toScheme, f ≫ U.ι = x := by
  let U : S.Opens := ⨅ i, L i
  have hU : IsClosed (U : Set S) := by
    change IsClosed ((⨅ i, L i : S.Opens) : Set S)
    rw [Opens.coe_iInf]
    exact isClosed_iInter hL
  refine ⟨U, hU, ?_⟩
  intro T x
  simp only [ClopenLocusGluing.openImmersion_unique_lift_iff_range, Scheme.Opens.range_ι]
  constructor
  · intro h y hy
    change y ∈ ((⨅ i, L i : S.Opens) : Set S)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun i => h i hy)
  · intro h i y hy
    have hv := h hy
    change y ∈ ((⨅ i, L i : S.Opens) : Set S) at hv
    rw [Opens.coe_iInf] at hv
    exact Set.mem_iInter.mp hv i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ClopenLocusIntersection
