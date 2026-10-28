import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientSchemeTests
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra

/-! # Dual Lift Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftReduction

noncomputable section

/-! The actual reduction equation for an affine scheme lift is exactly
the first-coefficient equation of its recovered algebra homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]

theorem affineDualLift_reduction_iff (q : B →ₐ[k] C)
    (f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B) :
    Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ↔
      (TrivSqZeroExt.fstHom k C C).comp (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) B f) = q := by
  constructor
  · intro h
    have hs := congrArg Over.Hom.left h
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k C C).toRingHom) ≫ f.left =
      Spec.map (CommRingCat.ofHom q.toRingHom) at hs
    rw [← OverMorphismAlgebra.affineOverMorphismAlgebra_spec k (DualNumber C) B f, ← Spec.map_comp] at hs
    have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
    exact AlgHom.ext (fun b => RingHom.congr_fun hr b)
  · intro h
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k C C).toRingHom) ≫ f.left =
      Spec.map (CommRingCat.ofHom q.toRingHom)
    rw [← OverMorphismAlgebra.affineOverMorphismAlgebra_spec k (DualNumber C) B f, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom h

def affineDualLiftAlgebraEquiv (q : B →ₐ[k] C) :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k B C q} ≃
      {f : B →ₐ[k] DualNumber C // (TrivSqZeroExt.fstHom k C C).comp f = q} :=
  Equiv.subtypeEquiv (OverMorphismAlgebra.affineOverMorphismAlgebraEquiv k (DualNumber C) B)
    (affineDualLift_reduction_iff k B C q)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftReduction
