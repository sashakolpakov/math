import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.TangentUniversalComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.GlobalProduct

/-! # Universal Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The native affine universal family has the literal affine base
used by the constructed linear tangent obstruction. Its tangent pullback
is isomorphic to the family classified by that same actual test map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (κ : K →+* ℂ)
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ R ⟶ M.complexFiber κ)

abbrev Models.FinePELModel.affineUniversalFamily : Over (Spec (.of R)) := (M.complexTestFamily κ f).polarized.abelian.scheme

instance Models.FinePELModel.affineUniversalFamily_group : GrpObj (M.affineUniversalFamily κ R f) :=
  (M.complexTestFamily κ f).polarized.abelian.group

instance Models.FinePELModel.affineUniversalFamily_comm : IsCommMonObj (M.affineUniversalFamily κ R f) :=
  (M.complexTestFamily κ f).polarized.abelian.commutative

instance Models.FinePELModel.affineUniversalFamily_smooth : Smooth (M.affineUniversalFamily κ R f).hom :=
  inferInstanceAs (Smooth (M.complexTestFamily κ f).polarized.abelian.scheme.hom)

instance Models.FinePELModel.affineUniversalFamily_proper : IsProper (M.affineUniversalFamily κ R f).hom :=
  (M.complexTestFamily κ f).polarized.abelian.proper

instance Models.FinePELModel.affineUniversalFamily_connected : GeometricallyConnected (M.affineUniversalFamily κ R f).hom :=
  (M.complexTestFamily κ f).polarized.abelian.connected

def Models.FinePELModel.affineTangentFamilyComparison (d : Derivation ℂ R ℂ) :
    (M.universal.pullback (M.affineTangentClassifyingMap κ R f d)).polarized.abelian.scheme ≅
      TangentBasePoint.tangentFamily ℂ R (M.affineUniversalFamily κ R f) d :=
  (M.affineTangentUniversalComparison κ R f d).polarized.abelian

def Models.FinePELModel.affineClassifiedTangentProduct (U : (M.affineUniversalFamily κ R f).left.AffineOpenCover)
    (d : Derivation ℂ R ℂ) (a : FamilyTangent.Primitives.fixedFamilyDerivationGauges R (M.affineUniversalFamily κ R f) U)
    (ha : FamilyTangent.Primitives.IsFamilyTangentDerivationPrimitive R (M.affineUniversalFamily κ R f) U d a) :
    (M.universal.pullback (M.affineTangentClassifyingMap κ R f d)).polarized.abelian.scheme ≅
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (TangentBasePoint.fixedFamilyFiber ℂ R (M.affineUniversalFamily κ R f)) :=
  M.affineTangentFamilyComparison κ R f d ≪≫
    FamilyTangent.GlobalProduct.familyTangentGlobalProduct R (M.affineUniversalFamily κ R f) U d a ha

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
