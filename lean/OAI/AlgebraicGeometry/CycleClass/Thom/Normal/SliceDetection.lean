import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSupportedCupIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductSupportRetraction

/-! # Slice Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions

noncomputable section

/-! Restriction to the actual normal slice detects supported classes in an immersion chart. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

def tangentOrigin : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P := ⟨0, Metric.mem_ball_self P.radius_pos⟩

def firstInverseMap : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P) ⟶
    TopCat.of P.neighborhood :=
  (TopCat.isoOfHomeo (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P)).inv

theorem firstInverseMapsTo : Set.MapsTo (firstInverseMap P)
    (HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.tangentSupport (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P) ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ))
    P.relativeComplement := by
  intro y hy
  apply (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstMap_complement P (firstInverseMap P y)).mpr
  change (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) ((HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P).symm y) ∈ _
  rw [Homeomorph.apply_symm_apply]
  exact hy

def normalSliceMap : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) ⟶ TopCat.of P.neighborhood :=
  HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.tangentSection (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P) (tangentOrigin P) ≫
    firstInverseMap P

theorem normalSliceMapsTo : Set.MapsTo (normalSliceMap P) ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ)
    P.relativeComplement :=
  (firstInverseMapsTo P).comp
    (HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.tangentSection_mapsTo (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P)
      (tangentOrigin P) ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ))

def normalSliceCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P))
      ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) P.relativeComplement n :=
  HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.normalBallTangentSupportIso (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) E (ModuleCat.of ℚ ℚ) P.radius P.radius_pos
    ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ) n ≪≫
  AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) P.relativeComplement
    (HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.tangentSupport (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P) ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ))
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstMap_complement P) n

theorem normalSliceCohomologyIso_inv (n : ℕ) :
    (normalSliceCohomologyIso P n).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalSliceMap P) (normalSliceMapsTo P) n := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (firstInverseMap P) (firstInverseMapsTo P) n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.tangentSection (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P) (tangentOrigin P))
      (HodgeConjecture.DegreeTwo.ProductSupportRetraction.Constructions.tangentSection_mapsTo (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P)
        (tangentOrigin P) ({HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ)) n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

theorem normalSlice_pullback_injective (n : ℕ) : Function.Injective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalSliceMap P) (normalSliceMapsTo P) n) := by
  rw [← normalSliceCohomologyIso_inv]
  exact (normalSliceCohomologyIso P n).toLinearEquiv.symm.injective

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions
