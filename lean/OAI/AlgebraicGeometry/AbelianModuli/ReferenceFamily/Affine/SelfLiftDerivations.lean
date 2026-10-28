import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal

/-! # Self Lift Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.SelfLiftDerivations

noncomputable section

/-! Actual self-lifts of an affine coefficient scheme are exactly
derivations of its coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k C : Type) [CommRing k] [CommRing C] [Algebra k C]

theorem affineOverAlgHom_id : AlgebraAutomorphismNaturality.affineOverAlgHom k C C (AlgHom.id k C) = 𝟙 (EtaleSplittingAt.EtaleSplitting.affineOver k C) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id C)) = 𝟙 (Spec (.of C))
  exact Spec.map_id (CommRingCat.of C)

theorem affineOverAlgHom_self :
    AlgebraAutomorphismNaturality.affineOverAlgHom k C C (IsScalarTower.toAlgHom k C C) = 𝟙 (EtaleSplittingAt.EtaleSplitting.affineOver k C) :=
  affineOverAlgHom_id k C

def affineSelfLiftDerivationEquiv :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k C // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = 𝟙 _} ≃
      Derivation k C C :=
  (Equiv.subtypeEquivRight (fun f =>
    show (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = 𝟙 _) ↔
      (Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = AlgebraAutomorphismNaturality.affineOverAlgHom k C C (IsScalarTower.toAlgHom k C C)) by
        rw [affineOverAlgHom_self])).trans (DualLiftConormal.affineDualLiftDerivationEquiv k C C)

theorem affineSelfLiftDerivationEquiv_apply
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k C // Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ f = 𝟙 _})
    (c : C) : affineSelfLiftDerivationEquiv k C f c =
      (OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber C) C f.val c).snd :=
  DualLiftConormal.affineDualLiftDerivationEquiv_apply k C C _ c

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.SelfLiftDerivations
