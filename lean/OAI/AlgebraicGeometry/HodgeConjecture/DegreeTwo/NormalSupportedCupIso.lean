import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalHomologyProduct
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupCrossEvaluation
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Normal Supported Cup Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportedCupIso.Constructions

noncomputable section

/-!
# DegreeTwo: the actual local Thom cup is an isomorphism in every degree

The normal generator, the genuine relative cross-product equivalence, and
the actual relative universal coefficient theorem give an isomorphism.
The cup–cross identity identifies its map with the original supported cup.
The tangential open complement is arbitrary.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable (c : ℕ) (Y : TopCat.{0}) (B : Set Y) (hB : IsOpen B) (q : ℕ)

def normalSupportedCohomologyIso :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q ≃ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ((Fin c → ℂ) × Y))
        (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) (2*c+q) :=
  (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ Y B q).trans
    ((NormalHomologyProduct.Constructions.normalHomologyProductIso c Y B hB q).symm.dualMap.trans
      (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of ((Fin c → ℂ) × Y))
        (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) (2*c+q)).symm)

theorem normalSupportedCohomologyIso_evaluation
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q)
    (w : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y B q) :
    CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of ((Fin c → ℂ) × Y))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) (2*c+q)
      (normalSupportedCohomologyIso c Y B hB q a) (NormalHomologyProduct.Constructions.normalHomologyProductIso c Y B hB q w) =
      CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ Y B q a w := by
  simp only [normalSupportedCohomologyIso, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]

theorem normalSupportedCohomologyIso_eq_cup
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    normalSupportedCohomologyIso c Y B hB q a =
      ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B
        isClosed_singleton.isOpen_compl hB (2*c) q (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) a := by
  apply (CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of ((Fin c → ℂ) × Y))
    (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B) (2*c+q)).injective
  apply LinearMap.ext
  intro z
  obtain ⟨w,rfl⟩ := (NormalHomologyProduct.Constructions.normalHomologyProductIso c Y B hB q).surjective z
  rw [normalSupportedCohomologyIso_evaluation, NormalHomologyProduct.Constructions.normalHomologyProductIso_apply]
  have he := ExteriorCupCrossEvaluation.Constructions.relativeExteriorCup_cross_evaluation (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B
    isClosed_singleton.isOpen_compl hB (2*c) q (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) a
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c) w
  have hn := CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_evaluation c
  change CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ))
    ({0}ᶜ : Set (Fin c → ℂ)) (2*c) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c) = 1 at hn
  rw [hn, one_mul] at he
  exact he.symm

theorem normalSupportedCup_bijective :
    Function.Bijective (fun a => ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B
      isClosed_singleton.isOpen_compl hB (2*c) q (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) a) := by
  have he : (fun a => ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (Fin c → ℂ)) Y ({0}ᶜ) B
      isClosed_singleton.isOpen_compl hB (2*c) q (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) a) =
      normalSupportedCohomologyIso c Y B hB q :=
    funext (fun a => (normalSupportedCohomologyIso_eq_cup c Y B hB q a).symm)
  rw [he]
  exact (normalSupportedCohomologyIso c Y B hB q).bijective

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportedCupIso.Constructions
