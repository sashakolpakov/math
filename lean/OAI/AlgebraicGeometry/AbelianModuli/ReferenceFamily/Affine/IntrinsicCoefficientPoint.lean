import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.SelfLiftDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormal
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Intrinsic Coefficient Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IntrinsicCoefficientPoint

noncomputable section

section

/-! Derivations on any actual affine open of a smooth group identify
with coefficient-valued functionals on its constructed identity conormal.
The construction first realizes a derivation as an actual scheme lift,
then translates that lift to the group identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (C : Type) [CommRing C] [Algebra k C]
    (A : Over (Spec (.of k))) (i : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ A)

def openAffineLiftReference : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A :=
  Dual.CoefficientSchemeTests.dualCoefficientProjection k C ≫ i

theorem openAffineLiftReference_reduction :
    Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ openAffineLiftReference k C A i = i := by
  change Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ (Dual.CoefficientSchemeTests.dualCoefficientProjection k C ≫ i) = i
  rw [← Category.assoc, Dual.CoefficientSchemeTests.dualCoefficientOrigin_projection, Category.id_comp]

variable [IsOpenImmersion i.left]

def openAffineLiftDerivationEquiv :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ A // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = i} ≃ Derivation k C C :=
  (Equiv.subtypeEquivRight (fun f =>
    show (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = i) ↔ (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = (𝟙 _ : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ _) ≫ i) by
      rw [Category.id_comp])).trans
    ((Open.ImmersionLiftFibers.openImmersionLiftFiberEquiv (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C) i (𝟙 _)).symm.trans
      (SelfLiftDerivations.affineSelfLiftDerivationEquiv k C))

variable [GrpObj A] [Smooth A.hom]

def openAffineDerivationConormalEquiv : Derivation k C C ≃ (Constructed.IdentityConormal.constructedIdentityConormal k A →ₗ[k] C) :=
  (openAffineLiftDerivationEquiv k C A i).symm.trans
    ((Equiv.subtypeEquivRight (fun f =>
      show (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = i) ↔
        (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ openAffineLiftReference k C A i) by
          rw [openAffineLiftReference_reduction])).trans
      (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv k A C (openAffineLiftReference k C A i)))

end

/-! Coefficient points and their constant dual lifts agree with the
original native scheme points, through the literal complex-base isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest

def complexCoefficientBaseIso : EtaleSplittingAt.EtaleSplitting.affineOver ℂ ℂ ≅ Over.mk (𝟙 (Spec (.of ℂ))) :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 (Spec (.of ℂ))) ≫ 𝟙 (Spec (.of ℂ)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))
    rw [Category.id_comp]
    exact (Spec.map_id (CommRingCat.of ℂ)).symm)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ X) (q : B →ₐ[ℂ] ℂ)

theorem nativeAffineCoefficientPoint_eq : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i q =
    complexCoefficientBaseIso.inv ≫ (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B ℂ q ≫ i) := by
  apply Over.OverMorphism.ext
  change (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv B q).left ≫ i.left =
    (𝟙 (Spec (.of ℂ))) ≫ ((AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B ℂ q).left ≫ i.left)
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left, AlgebraAutomorphismNaturality.affineOverAlgHom_left, Category.id_comp]
  rfl

theorem complexDualCoefficientProjection :
    Dual.CoefficientSchemeTests.dualCoefficientProjection ℂ ℂ = toUnit (LieRanks.dualNumberTest ℂ) ≫ complexCoefficientBaseIso.inv := by
  apply (cancel_mono complexCoefficientBaseIso.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact toUnit_unique _ _

theorem nativeAffineCoefficientPoint_constant :
    openAffineLiftReference ℂ ℂ X (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B ℂ q ≫ i) =
      toUnit (LieRanks.dualNumberTest ℂ) ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i q := by
  change Dual.CoefficientSchemeTests.dualCoefficientProjection ℂ ℂ ≫ (AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B ℂ q ≫ i) = _
  rw [complexDualCoefficientProjection, Category.assoc, nativeAffineCoefficientPoint_eq]

variable [GrpObj X]

theorem nativeAffineCoefficientPoint_one (h : AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B ℂ q ≫ i = 1) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B i q = (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  rw [nativeAffineCoefficientPoint_eq, h, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IntrinsicCoefficientPoint
