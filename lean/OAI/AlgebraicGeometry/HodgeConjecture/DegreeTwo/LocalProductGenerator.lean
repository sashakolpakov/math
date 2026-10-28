import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity

/-! # Local Product Generator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions

noncomputable section

/-!
# DegreeTwo: an actual nonzero local product class

Cross the specified tangent and normal local homology generators. The
proved relative cross-product retraction shows this is nonzero, and its
support is exactly the origin in the product coordinate space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles

theorem normalRationalHomologyGenerator_ne_zero (p : ℕ) :
    CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator p ≠ 0 := by
  intro h
  have hn := CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator_normalization p
  rw [h, map_zero] at hn
  exact zero_ne_one hn

def localProductCrossGenerator (d c : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) (0,0) (2*d + 2*c) :=
  (eqToHom (congrArg
    (fun A => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) A (2*d + 2*c))
    (RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) 0 0)))
      (RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ))
        ({0}ᶜ) ({0}ᶜ) (2*d) (2*c)
        (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c))

theorem localProductCrossGenerator_ne_zero (d c : ℕ) : localProductCrossGenerator d c ≠ 0 := by
  have hn := RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass_ne_zero
    (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) ({0}ᶜ) ({0}ᶜ) (2*d) (2*c)
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl
    (normalRationalHomologyGenerator_ne_zero d) (normalRationalHomologyGenerator_ne_zero c)
  intro hz
  apply hn
  have hi := (ModuleCat.mono_iff_injective
    (eqToHom (congrArg
      (fun A => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of ((Fin d → ℂ) × (Fin c → ℂ))) A (2*d + 2*c))
      (RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin d → ℂ)) (TopCat.of (Fin c → ℂ)) 0 0)))).mp
    inferInstance
  exact hi (hz.trans (map_zero _).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions
