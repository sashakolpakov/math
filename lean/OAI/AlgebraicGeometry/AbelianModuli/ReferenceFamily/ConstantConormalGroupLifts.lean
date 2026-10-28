import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalRatio
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalCoefficientSquare
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslatedConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates

/-! # Constant Conormal Group Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantConormalGroupLifts

noncomputable section

/-! Extending an original identity tangent to a coefficient algebra
and translating by an arbitrary reference gives exactly the constant
native conormal coordinates. The original group-valued lift is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest
attribute [local irreducible] Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral G.left] [Smooth G.hom] [GrpObj G]
    (C : Type) [CommRing C] [Algebra ℂ C]

def constantIdentityConormalLift (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ G // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ f =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (1 : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ G)} := by
  let f := (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ G ℂ 1).symm l
  let q := Algebra.ofId ℂ C
  let Q := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber ℂ) (DualNumber C) (Dual.NumberCoefficients.dualNumberAlgMap q)
  refine ⟨Q ≫ f.val, ?_⟩
  have he := Dual.CoefficientMapSquares.dualCoefficientOrigin_natural ℂ ℂ C q
  calc
    Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (Q ≫ f.val) =
        Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ ℂ C q ≫ (Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ f.val) := by
      rw [← Category.assoc, he, Category.assoc]
    _ = _ := by rw [f.property, MonObj.comp_one, MonObj.comp_one, MonObj.comp_one]

omit [IsIntegral G.left] in
theorem constantIdentityConormalLift_coordinates (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ G C 1 (constantIdentityConormalLift G C l) = ConormalUnitLogCoordinates.coefficientCovector C l := by
  apply LinearMap.ext
  intro z
  have h := Constructed.ConormalCoefficientSquare.constructedIdentityLiftConormalEquiv_square ℂ G ℂ C (Algebra.ofId ℂ C) 1 1
    ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ G ℂ 1).symm l) (constantIdentityConormalLift G C l)
    (MonObj.comp_one _) rfl z
  rw [Equiv.apply_symm_apply] at h
  exact h

def constantTranslatedConormalLift (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ G) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ G // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ c} :=
  Constructed.ConormalRatio.constructedConormalTranslatedLift ℂ G C c (constantIdentityConormalLift G C l)

omit [IsIntegral G.left] in
theorem constantTranslatedConormalLift_coordinates (l : Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ G) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ G C c (constantTranslatedConormalLift G C l c) = ConormalUnitLogCoordinates.coefficientCovector C l :=
  (Constructed.ConormalRatio.constructedIdentityLiftConormalEquiv_translate ℂ G C c (constantIdentityConormalLift G C l)).trans
    (constantIdentityConormalLift_coordinates G C l)

theorem constantIdentityConormalLift_native
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ) :
    (constantIdentityConormalLift G C (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear G v)).val =
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber ℂ) (DualNumber C) (Dual.NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ C)) ≫
        (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v).val := by
  have h := Intrinsic.TranslatedConormal.constructedIdentityLiftConormalEquiv_native_inverse G v 1
  rw [mul_one] at h
  exact congrArg (fun f => Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber ℂ) (DualNumber C)
    (Dual.NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ C)) ≫ f) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantConormalGroupLifts
