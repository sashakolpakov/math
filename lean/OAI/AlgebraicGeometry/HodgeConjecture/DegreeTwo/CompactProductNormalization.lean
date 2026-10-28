import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductCoefficient

/-! # Compact Product Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductNormalization.Constructions

noncomputable section

/-! The actual compact exterior product of normalized point classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem compactExteriorCup_point (d c : ℕ) :
    CompactExteriorCup.Constructions.compactExteriorCup (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) (2*d) (2*c)
      (CompactPointNormalization.Constructions.compactPointDualClass d) (CompactPointNormalization.Constructions.compactPointDualClass c) =
    CompactPointNaturality.Constructions.compactPointCohomologyι (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) (0,0) (2*d+2*c)
      (LocalProductCup.Constructions.localProductCupClass d c) := by
  unfold CompactPointNormalization.Constructions.compactPointDualClass
  rw [CompactExteriorCup.Constructions.compactExteriorCup_stage, CompactExteriorCup.Constructions.compactExteriorCupStage_apply]
  have hK : (⟨{0},isCompact_singleton⟩ ×ˢ ⟨{0},isCompact_singleton⟩ :
      Compacts ((Fin d → ℂ) × (Fin c → ℂ))) = ⟨{(0,0)},isCompact_singleton⟩ := by
    apply Compacts.ext
    exact Set.singleton_prod_singleton
  exact CompactPointNaturality.Constructions.compactSupportCohomologyι_supportCast _ _ _ hK _
    (CompactExteriorCup.Constructions.compactProductComplement _ _ _ _)
    (RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) 0 0)
    (2*d+2*c) _

def compactProductPointTop (d c : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) (2*(d+c)) :=
  eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ)))) (Nat.mul_add 2 d c).symm)
    (CompactExteriorCup.Constructions.compactExteriorCup (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) (2*d) (2*c)
      (CompactPointNormalization.Constructions.compactPointDualClass d) (CompactPointNormalization.Constructions.compactPointDualClass c))

theorem compactProductPointTop_local (d c : ℕ) :
    compactProductPointTop d c =
    CompactPointNaturality.Constructions.compactPointCohomologyι (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) 0 (2*(d+c))
      (LocalProductCoefficient.Constructions.localProductCupTop d c) := by
  unfold compactProductPointTop
  rw [compactExteriorCup_point,
    CompactPointNaturality.Constructions.compactPointCohomologyι_degreeCast _ _ (Nat.mul_add 2 d c).symm]
  rfl

theorem compactProductPointTop_normalization (d c : ℕ) :
    compactProductPointTop d c = LocalProductCoefficient.Constructions.localProductCupCoefficient d c •
      (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
        (LocalProductCoefficient.Constructions.productFlattenCoordinates d c).toHomeomorph (2*(d+c))).hom
        (CompactPointNormalization.Constructions.compactPointDualClass (d+c)) := by
  rw [compactProductPointTop_local, LocalProductCoefficient.Constructions.localProductCupTop_eq_smul, map_smul,
    CompactPointNaturality.Constructions.compactCoordinatePointClass]

theorem compactProductPointTop_ne_zero (d c : ℕ) : compactProductPointTop d c ≠ 0 := by
  let e : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Fin (d+c) → ℂ)) (2*(d+c)) ≅
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) (2*(d+c)) :=
    AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (LocalProductCoefficient.Constructions.productFlattenCoordinates d c).toHomeomorph (2*(d+c))
  have hn : e.hom (CompactPointNormalization.Constructions.compactPointDualClass (d+c)) ≠ 0 :=
    CompactPointNaturality.Constructions.moduleIso_hom_ne_zero e (CompactPointNormalization.Constructions.compactPointDualClass (d+c)) (CompactPointNormalization.Constructions.compactPointDualClass_ne_zero (d+c))
  rw [compactProductPointTop_normalization]
  exact smul_ne_zero (LocalProductCoefficient.Constructions.localProductCupCoefficient_ne_zero d c) hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductNormalization.Constructions
