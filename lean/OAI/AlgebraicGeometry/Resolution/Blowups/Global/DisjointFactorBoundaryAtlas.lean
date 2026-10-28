import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AtlasFromAffineCover
import OAI.AlgebraicGeometry.Resolution.Blowups.ComaximalFactorBoundaryCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.BlowupBoundaryCenter

/-! # Disjoint Factor Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Blowing up one disjoint center factor preserves the global boundary atlas of the remaining factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.disjointFactorBlowup
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hI : I = K * L) (hdisjoint : K ⊔ L = ⊤) :
    CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f) (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK D) := by
  let AK := A.comaximalFactor K L hI hdisjoint
  let AL := A.comaximalFactor L K (hI.trans (mul_comm K L)) ((sup_comm L K).trans hdisjoint)
  let Q := AK.reesCover hK
  let : ∀ i, Algebra ℂ Γ(X, AK.opens i) := fun i => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (AK.opens i)
  let : ∀ p : Q.I₀, Algebra ℂ (Q.X p) := fun p =>
    Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra ℂ (K.ideal (AK.opens p.1)) p.2
  let v (p : Q.I₀) : Option β → Q.X p :=
    MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (K.ideal (AK.opens p.1)) p.2 (AK.divided p.1)
      (AK.equations p.1) (AK.contained p.1)
  have hb (p : Q.I₀) : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (Q.X p) (v p) :=
    MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, AK.opens p.1))
      (K.ideal (AK.opens p.1)) (AK.equations p.1) (AK.divided p.1) (AK.contained p.1)
      (AK.boundary p.1) (AK.center p.1) p.2
  apply CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofAffineCover (GlobalBlowup.Data.Construction.globalBlowupToBase K hK ≫ f)
    (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK D) Q
    (fun p => GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f K hK (AK.opens p.1) p.2)
    (fun p => (L.ideal (AK.opens p.1)).map (Blowup.Charts.Construction.blowupChartConstants (K.ideal (AK.opens p.1)) p.2))
    v (fun p => (AL.divided p.1).map Function.Embedding.some)
  · intro p
    exact GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart K L hK (AK.opens p.1) p.2
  · intro p j
    exact CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart K hK D (AK.divided p.1) (AK.opens p.1)
      (AK.equations p.1) (AK.component p.1) (AK.contained p.1) p.2 (hb p) j
  · exact hb
  · intro p
    exact (AL.center p.1).disjointBlowup (.of Γ(X, AK.opens p.1))
      (K.ideal (AK.opens p.1)) (L.ideal (AK.opens p.1)) p.2 (AK.equations p.1)
      (AK.divided p.1) (AL.divided p.1) (AK.contained p.1)
      (congrArg (fun J : X.IdealSheafData => J.ideal (AK.opens p.1)) hdisjoint)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
