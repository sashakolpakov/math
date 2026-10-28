import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.TangentClassifyingMaps

/-! # Tangent Universal Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The family classified by an actual tangent test is the actual
pullback of the original affine test family. The comparison retains all
PEL structure through the proved pullback-composition isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (κ : K →+* ℂ)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ R ⟶ M.complexFiber κ)

def Models.FinePELModel.affineTangentUniversalComparison (d : Derivation ℂ R ℂ) :
    PEL.Objects.PELIso (M.universal.pullback (M.affineTangentClassifyingMap κ R f d))
      ((M.complexTestFamily κ f).pullback (Complex.BaseMaps.complexBaseRestrictionMap κ (Affine.BaseTangentTests.affineBaseTangentTest ℂ R d))) := by
  unfold Models.FinePELModel.affineTangentClassifyingMap
  rw [Models.FinePELModel.complexFamilyBaseMap_comp]
  exact PEL.Objects.PELIso.pullbackComp M.universal (M.complexFamilyBaseMap κ f)
    (Complex.BaseMaps.complexBaseRestrictionMap κ (Affine.BaseTangentTests.affineBaseTangentTest ℂ R d))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
