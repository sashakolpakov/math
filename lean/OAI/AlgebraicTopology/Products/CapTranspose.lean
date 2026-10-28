import OAI.AlgebraicTopology.Products.OrdinaryRelativeCapAdjunction
import OAI.AlgebraicTopology.Products.RelativeCupGradedCommutativity
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD
import OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology
import OAI.AlgebraicTopology.Products.CupGradedCommutativity

/-! # Cap Transpose -/

namespace OAI.AlgebraicTopology.Products.CapTranspose

noncomputable section

/-!
# Transposition of the actual cap pairings

Evaluation of a relative class on the ordinary-relative cap is the signed
evaluation of the ordinary class on the support-relative cap. The sign
comes from the proved graded commutativity of the actual relative cup.
All degree identifications below use equality transport on the existing
cohomology and homology objects.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Relative evaluation moves a cohomology degree transport to the inverse
degree transport on the actual integral homology argument. -/
theorem relativeRationalHomologyEvaluation_cohomologyCast
    (X : TopCat.{0}) (B : Set X) {m n : ℕ} (h : m = n)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B m)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B n) :
    Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X B n
        (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X B h c) z =
      Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X B m c
        ((eqToHom (congrArg (fun i => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B i) h.symm)) z) := by
  subst n
  rfl

/-- The analogous equality transport for ordinary rational evaluation. -/
theorem singularEvaluation_cohomologyCast
    (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X m)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X n
        (CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) h c) z =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X m c
        ((eqToHom (congrArg
          (fun i => (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology i) h.symm)) z) := by
  subst n
  rfl

/-- The actual coefficient map commutes with equality transport in degree. -/
theorem integralToRationalHomology_degreeCast
    (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology m) :
    Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n
        ((eqToHom (congrArg (fun i => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology i) h)) z) =
      (eqToHom (congrArg (fun i => (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology i) h))
        (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X m z) := by
  subst n
  rfl

/-- Ordinary cap transposition on the genuine rational (co)homology groups. -/
theorem ordinaryCapTranspose (X : TopCat.{0}) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (p + q)) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X q b
        (CapBoundary.singularCapHomology X p q a z) =
      (-1 : ℚ) ^ (p * q) *
        Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
          (CapBoundary.singularCapHomology X q p b
            ((eqToHom (congrArg
              (fun n => (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n)
              (Nat.add_comm p q))) z)) := by
  calc
    _ = Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (p + q)
        (CupCohomology.singularCohomologyCup X p q a b) z :=
      (CapCompatibility.singularCohomologyCup_evaluation_cap X p q a b z).symm
    _ = (-1 : ℚ) ^ (p * q) *
        Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (q + p)
          (CupCohomology.singularCohomologyCup X q p b a)
          ((eqToHom (congrArg
            (fun n => (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n)
            (Nat.add_comm p q))) z) := by
      rw [CupGradedCommutativity.singularCohomologyCup_graded_comm, map_smul, LinearMap.smul_apply]
      change (-1 : ℚ) ^ (p * q) *
        Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (p + q)
          (CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ)
            (Nat.add_comm q p) (CupCohomology.singularCohomologyCup X q p b a)) z = _
      rw [singularEvaluation_cohomologyCast]
    _ = _ := by rw [CapCompatibility.singularCohomologyCup_evaluation_cap]

/-- The same ordinary cap transposition for an actual integral homology
input and the established integral-to-rational coefficient map. -/
theorem mixedCapTranspose (X : TopCat.{0}) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X q b
        (Duality.Poincare.MixedCapHomology.mixedSingularCapHomology X p q a z) =
      (-1 : ℚ) ^ (p * q) *
        Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
          (Duality.Poincare.MixedCapHomology.mixedSingularCapHomology X q p b
            ((eqToHom (congrArg
              (fun n => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) (Nat.add_comm p q))) z)) := by
  rw [Duality.Poincare.MixedCapHomology.mixedSingularCapHomology_apply, Duality.Poincare.MixedCapHomology.mixedSingularCapHomology_apply]
  calc
    _ = (-1 : ℚ) ^ (p * q) *
        Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
          (CapBoundary.singularCapHomology X q p b
            ((eqToHom (congrArg
              (fun n => (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n)
              (Nat.add_comm p q)))
              (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (p + q) z))) :=
      ordinaryCapTranspose X p q a b
        (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (p + q) z)
    _ = _ := congrArg
      (fun w : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (q + p) =>
        (-1 : ℚ) ^ (p * q) * Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
          (CapBoundary.singularCapHomology X q p b w))
      (integralToRationalHomology_degreeCast X (Nat.add_comm p q) z).symm

/-- Relative cap transposition with the canonical universal-coefficient
evaluation on the rational relative output. The source is the actual
integral relative homology, with the total-degree transport shown. -/
theorem relativeCapTranspose (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X B q b
        (Duality.Poincare.CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q a z) =
      (-1 : ℚ) ^ (p * q) *
        Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
          (Duality.Poincare.SupportRelativeCap.relativeCapHomology X B q p b
            ((eqToHom (congrArg
              (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B n) (Nat.add_comm p q))) z)) := by
  rw [AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_apply, OrdinaryRelativeCapAdjunction.ordinaryRelativeCapHomology_evaluation]
  calc
    _ = (-1 : ℚ) ^ (p * q) *
        Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X B (q + p)
          (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup X B q p b a)
          ((eqToHom (congrArg
            (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B n) (Nat.add_comm p q))) z) := by
      rw [RelativeCupGradedCommutativity.absoluteRelativeCohomologyCup_graded_comm, map_smul, LinearMap.smul_apply]
      change (-1 : ℚ) ^ (p * q) *
        Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X B (p + q)
          (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of ℚ ℚ) X B (Nat.add_comm q p)
            (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup X B q p b a)) z = _
      rw [relativeRationalHomologyEvaluation_cohomologyCast]
    _ = _ := by rw [AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction.Cycles.relativeAbsoluteCohomologyCup_evaluation_cap]

/-- If the product of the two degrees is even, relative cap transposition
has no sign. -/
theorem relativeCapTranspose_of_even
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ) (hpq : Even (p * q))
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X B q b
        (Duality.Poincare.CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q a z) =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
        (Duality.Poincare.SupportRelativeCap.relativeCapHomology X B q p b
          ((eqToHom (congrArg
            (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B n) (Nat.add_comm p q))) z)) := by
  rw [relativeCapTranspose, hpq.neg_one_pow, one_mul]

/-- In particular, an even ordinary degree gives the unsigned identity. -/
theorem relativeCapTranspose_of_even_left
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ) (hp : Even p)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X B q b
        (Duality.Poincare.CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q a z) =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
        (Duality.Poincare.SupportRelativeCap.relativeCapHomology X B q p b
          ((eqToHom (congrArg
            (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B n) (Nat.add_comm p q))) z)) :=
  relativeCapTranspose_of_even X B hB p q (hp.mul_right q) a b z

/-- An even relative degree also gives the unsigned identity. -/
theorem relativeCapTranspose_of_even_right
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ) (hq : Even q)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X B q b
        (Duality.Poincare.CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q a z) =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
        (Duality.Poincare.SupportRelativeCap.relativeCapHomology X B q p b
          ((eqToHom (congrArg
            (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B n) (Nat.add_comm p q))) z)) :=
  relativeCapTranspose_of_even X B hB p q (hq.mul_left p) a b z

/-- The ordinary mixed cap identity is also unsigned in even total parity. -/
theorem mixedCapTranspose_of_even (X : TopCat.{0}) (p q : ℕ) (hpq : Even (p * q))
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X q b
        (Duality.Poincare.MixedCapHomology.mixedSingularCapHomology X p q a z) =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X p a
        (Duality.Poincare.MixedCapHomology.mixedSingularCapHomology X q p b
          ((eqToHom (congrArg
            (fun n => (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) (Nat.add_comm p q))) z)) := by
  rw [mixedCapTranspose, hpq.neg_one_pow, one_mul]

end

end OAI.AlgebraicTopology.Products.CapTranspose
