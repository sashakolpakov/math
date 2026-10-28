import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingleKunnethComponent
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeProductEquivalence
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity

/-! # Normal Homology Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalHomologyProduct.Constructions

noncomputable section

/-! Crossing with the specified normal generator is an actual relative homology isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles
open scoped TensorProduct DirectSum

set_option backward.isDefEq.respectTransparency false

def normalTensorGeneratorEquiv (c : ℕ) (W : ModuleCat.{0} ℚ) :
    W ≃ₗ[ℚ] (CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin c → ℂ)) 0 (2*c) ⊗[ℚ] W) :=
  (TensorProduct.lid ℚ W).symm.trans
    (TensorProduct.congr (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv c).symm (LinearEquiv.refl ℚ W))

theorem normalTensorGeneratorEquiv_apply (c : ℕ) (W : ModuleCat.{0} ℚ) (w : W) :
    normalTensorGeneratorEquiv c W w = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c ⊗ₜ[ℚ] w := by
  simp only [normalTensorGeneratorEquiv, LinearEquiv.trans_apply,
    TensorProduct.lid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rfl

def normalHomologyProductIso (c : ℕ) (Y : TopCat.{0}) (B : Set Y) (hB : IsOpen B) (q : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q ≃ₗ[ℚ]
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of ((Fin c → ℂ) × Y))
        (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) (2*c+q) :=
  (normalTensorGeneratorEquiv c (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q)).trans
    ((SingleKunnethComponent.Constructions.algebraicKunnethSingleLeftComponent
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin c → ℂ)) ({0}ᶜ)) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B)
      (2*c) q (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalLocalHomology_isZero c)).trans
      (RelativeProductEquivalence.Constructions.relativeCrossHomologyIso (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B
        isClosed_singleton.isOpen_compl hB (2*c+q)).toLinearEquiv)

theorem normalHomologyProductIso_apply (c : ℕ) (Y : TopCat.{0}) (B : Set Y) (hB : IsOpen B)
    (q : ℕ) (w : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    normalHomologyProductIso c Y B hB q w =
      RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B (2*c) q
        (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c) w := by
  rw [normalHomologyProductIso, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    normalTensorGeneratorEquiv_apply, SingleKunnethComponent.Constructions.algebraicKunnethSingleLeftComponent_apply]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalHomologyProduct.Constructions
