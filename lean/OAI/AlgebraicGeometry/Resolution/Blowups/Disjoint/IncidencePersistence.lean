import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DisjointFactorBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformIncidenceTransform

/-! # Incidence Persistence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Constant incidence on a remaining subcenter persists through a disjoint blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.disjointFactorBlowup_incidence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hI : I = K * L) (hdisjoint : K ⊔ L = ⊤)
    (H : X.IdealSheafData) (F : Finset β)
    (hF : ∀ i, H.ideal (A.opens i) ≠ ⊤ → A.divided i = F) :
    ∀ p : (A.disjointFactorBlowup K L hK hI hdisjoint).indices,
      (H.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)).ideal
        ((A.disjointFactorBlowup K L hK hI hdisjoint).opens p) ≠ ⊤ →
      (A.disjointFactorBlowup K L hK hI hdisjoint).divided p = F.map Function.Embedding.some := by
  intro p hp
  let R : CommRingCat := .of (Blowup.Charts.Construction.blowupChart (K.ideal (A.opens p.1)) p.2)
  let j := GlobalControlled.Chart.Construction.globalBlowupReesChart K hK (A.opens p.1) p.2
  let : IsOpenImmersion j := GlobalControlled.Chart.Construction.globalBlowupReesChart_isOpenImmersion K hK (A.opens p.1) p.2
  have hH : (H.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel ((H.ideal (A.opens p.1)).map (Blowup.Charts.Construction.blowupChartConstants (K.ideal (A.opens p.1)) p.2)) :=
    GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart K H hK (A.opens p.1) p.2
  have hproper : H.ideal (A.opens p.1) ≠ ⊤ := by
    intro ht
    apply hp
    change (H.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)).ideal (Affine.OpenBoundaryTransport.Construction.specOpenImage R j) = ⊤
    rw [Global.AtlasFromAffineCover.Construction.specOpenSectionEquiv_ideal_map_symm R j _ _ hH, ht, Ideal.map_top, Ideal.map_top]
  change (A.divided p.1).map Function.Embedding.some = F.map Function.Embedding.some
  rw [hF p.1 hproper]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
