import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MapConstantReduction

/-! # Dual Lift Deformed Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftDeformedPullback

noncomputable section

/-! Pullback of actual affine lifts by a deformed coefficient map
retains the original scheme composition. Differences of their actual
derivations depend only on the reduced coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k A B : Type) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (f : DualNumber A →ₐ[k] DualNumber B)
    (hred : ∀ u, (f u).fst = algebraMap A B u.fst)

def affineDualLiftDeformedPullback
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber A) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k A ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k A A (IsScalarTower.toAlgHom k A A)}) :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k B ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k A B (IsScalarTower.toAlgHom k A B)} := by
  let g := f.comp (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber A) A u.val)
  refine ⟨AlgebraAutomorphismNaturality.affineOverAlgHom k A (DualNumber B) g, ?_⟩
  apply (DualLiftReduction.affineDualLift_reduction_iff k A B (IsScalarTower.toAlgHom k A B) _).mpr
  rw [OverMorphismAlgebra.affineOverMorphismAlgebra_ofAlgHom]
  apply AlgHom.ext
  intro a
  have hu := AlgHom.congr_fun
    ((DualLiftReduction.affineDualLift_reduction_iff k A A (IsScalarTower.toAlgHom k A A) u.val).mp u.property) a
  change (f (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber A) A u.val a)).fst = algebraMap A B a
  rw [hred]
  exact congrArg (algebraMap A B) hu

theorem affineDualLiftDeformedPullback_value
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber A) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k A ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k A A (IsScalarTower.toAlgHom k A A)}) :
    (affineDualLiftDeformedPullback k A B f hred u).val =
      AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber A) (DualNumber B) f ≫ u.val := by
  rw [← OverMorphismAlgebra.affineOverMorphismAlgebra_recovery k (DualNumber A) A u.val, OverMorphismAlgebra.affineOverAlgHom_comp]
  rfl

theorem affineDualLiftDeformedPullback_derivation
    (u : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber A) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k A ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k A A (IsScalarTower.toAlgHom k A A)})
    (a : A) :
    DualLiftConormal.affineDualLiftDerivationEquiv k A B (affineDualLiftDeformedPullback k A B f hred u) a =
      (f (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber A) A u.val a)).snd := by
  rw [DualLiftConormal.affineDualLiftDerivationEquiv_apply]
  change (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber B) A
    (AlgebraAutomorphismNaturality.affineOverAlgHom k A (DualNumber B)
      (f.comp (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber A) A u.val))) a).snd = _
  rw [OverMorphismAlgebra.affineOverMorphismAlgebra_ofAlgHom]
  rfl

theorem affineDualLiftDeformedPullback_difference
    (heps : f DualNumber.eps = DualNumber.eps)
    (u v : {u : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber A) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k A //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin k A ≫ u = AlgebraAutomorphismNaturality.affineOverAlgHom k A A (IsScalarTower.toAlgHom k A A)})
    (a : A) :
    DualLiftConormal.affineDualLiftDerivationEquiv k A B (affineDualLiftDeformedPullback k A B f hred u) a -
        DualLiftConormal.affineDualLiftDerivationEquiv k A B (affineDualLiftDeformedPullback k A B f hred v) a =
      algebraMap A B (DualLiftConormal.affineDualLiftDerivationEquiv k A A u a - DualLiftConormal.affineDualLiftDerivationEquiv k A A v a) := by
  rw [affineDualLiftDeformedPullback_derivation, affineDualLiftDeformedPullback_derivation,
    DualLiftConormal.affineDualLiftDerivationEquiv_apply, DualLiftConormal.affineDualLiftDerivationEquiv_apply]
  apply Dual.MapConstantReduction.dualMap_sameReduction_difference (IsScalarTower.toAlgHom k A B) f hred heps
  have hu := AlgHom.congr_fun
    ((DualLiftReduction.affineDualLift_reduction_iff k A A (IsScalarTower.toAlgHom k A A) u.val).mp u.property) a
  have hv := AlgHom.congr_fun
    ((DualLiftReduction.affineDualLift_reduction_iff k A A (IsScalarTower.toAlgHom k A A) v.val).mp v.property) a
  exact hu.trans hv.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftDeformedPullback
