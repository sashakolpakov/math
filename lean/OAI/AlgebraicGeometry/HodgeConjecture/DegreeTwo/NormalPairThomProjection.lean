import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSupportedCupIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupAssociativity

/-! # Normal Pair Thom Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairThomProjection.Constructions

noncomputable section

/-! The projection formula for the actual supported normal-pair Thom isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)
variable (B : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (hB : IsOpen B)

theorem normalPairTangent_pullback_rightCup (q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) r) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P)
      (A := NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (B := B) (fun _ hx => hx) (q+r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q r a b) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
      (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) q r
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P)
        (A := NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (B := B) (fun _ hx => hx) q a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P) r b) := by
  let _ := (inferInstance : NormedSpace ℝ E)
  exact CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCupWith_pullback (TopCat.of P.neighborhood)
    (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P) (fun _ hx => hx) q r a b

theorem normalPairSupportedCohomologyIso_projection (q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) r) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (NormalPairProductSupport.Constructions.normalPairCombinedComplement P B) (Nat.add_assoc (2*c) q r)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of P.neighborhood)
        (NormalPairProductSupport.Constructions.normalPairCombinedComplement P B) (2*c+q) r
        (PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P B hB q a)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P) r b)) =
      PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P B hB (q+r)
        (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q r a b) := by
  rw [PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso_eq_cup, PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso_eq_cup,
    normalPairTangent_pullback_rightCup]
  exact SupportCupAssociativity.Constructions.twoSupportCohomologyCup_right_assoc (TopCat.of P.neighborhood) P.relativeComplement
    (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P)
    (hB.preimage (NormalPairProductSupport.Constructions.normalPairTangentMap P).hom.continuous) P.rationalClassFin
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P)
      (A := NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (B := B) (fun _ hx => hx) q a)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P) r b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairThomProjection.Constructions
