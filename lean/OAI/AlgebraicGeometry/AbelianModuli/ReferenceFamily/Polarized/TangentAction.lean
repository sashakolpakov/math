import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPicardTangentMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PicardTangent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupTangentFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Lie

/-! # Tangent Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentAction

noncomputable section

/-! Composing the original polarization differential with the actual
Picard tangent comparison intertwines conjugate CM tangent action and
original structure-sheaf H1 pullback, by the literal Rosati square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

local instance polarizedH1TangentIntegral {n : ℕ} (G : HilbertConstruction.Abelian.Schemes.AbelianScheme n Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsIntegral G.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral G
local instance polarizedH1TangentModule : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.abelian.scheme

def polarizedStructureH1TangentLinear :
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1 :=
  (RepresentedPicardTangentBijection.representedPicardTangentLinear A.abelian A.dual).comp (Intrinsic.GroupConormalMap.nativeGroupTangentMap A.polarization.isogeny.hom)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) (hρ : ActionData.RosatiConjugation A ρ)

include hρ

theorem polarizedStructureH1TangentLinear_rosati (a : NumberField.RingOfIntegers E)
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.abelian.scheme.hom) → ℂ) :
    polarizedStructureH1TangentLinear A
        (Intrinsic.Lie.nativeLieDifferential A.abelian ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a) v) =
      StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a) (polarizedStructureH1TangentLinear A v) := by
  obtain ⟨d, hd, hp, hr⟩ := hρ a
  let : IsMonHom d := hd
  have ht := congrArg (fun f : A.abelian.scheme ⟶ A.dual.abelian.scheme => Intrinsic.GroupConormalMap.nativeGroupTangentMap f) hr
  rw [Intrinsic.GroupTangentFunctoriality.nativeGroupTangentMap_comp, Intrinsic.GroupTangentFunctoriality.nativeGroupTangentMap_comp] at ht
  have hv := LinearMap.congr_fun ht v
  have hP := RepresentedPicardTangentMorphism.representedPicardTangentLinear_morphism A.abelian A.abelian A.dual A.dual (ρ.map a) d hp
    (Intrinsic.GroupConormalMap.nativeGroupTangentMap A.polarization.isogeny.hom v)
  exact (congrArg (RepresentedPicardTangentBijection.representedPicardTangentLinear A.abelian A.dual) hv.symm).trans hP

theorem polarizedStructureH1TangentLinear_rosati_comp (a : NumberField.RingOfIntegers E) :
    (polarizedStructureH1TangentLinear A).comp
        (Intrinsic.Lie.nativeLieDifferential A.abelian ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a)) =
      (StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a)).comp (polarizedStructureH1TangentLinear A) :=
  LinearMap.ext (polarizedStructureH1TangentLinear_rosati A ρ hρ a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TangentAction
