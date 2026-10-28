import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductSupportRetraction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup

/-! # Supported Product Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedProductTest.Constructions

noncomputable section

/-!
# DegreeTwo: arbitrary tangentially supported tests in an actual product

Contracting the first factor preserves the entire tangential complement.
Consequently the actual supported cup with a first-factor class depends
only on the actual restriction of the test to the chosen section.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0})

theorem supportedFirstFactorCup_eq_exterior (x : X)
    (H : ContinuousMap.Homotopy (ContinuousMap.const X x) (ContinuousMap.id X))
    (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (Prod.snd ⁻¹' B) q) :
    SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
      (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X×Y) ⟶ X) (A := Prod.fst ⁻¹' A) (B := A)
        (fun _ hx => hx) p a) b =
    ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X Y x) (A := B) (B := Prod.snd ⁻¹' B) (fun _ hx => hx) q b) := by
  have hb := ProductSupportRetraction.Constructions.secondSupport_class_eq_pullback X Y (ModuleCat.of ℚ ℚ) x H B q b
  exact congrArg
    (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
      (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X×Y) ⟶ X) (A := Prod.fst ⁻¹' A) (B := A)
        (fun _ hx => hx) p a)) hb

variable [T2Space X] [T2Space Y]

def compactFirstFactorSupportedCup (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (Prod.snd ⁻¹' (L : Set Y)ᶜ) q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (p+q) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (K ×ˢ L) (p+q)
    (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (X×Y)) S (p+q)) (CompactExteriorCup.Constructions.compactProductComplement X Y K L))
      (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X×Y)) (Prod.fst ⁻¹' (K : Set X)ᶜ)
        (Prod.snd ⁻¹' (L : Set Y)ᶜ)
        (K.isCompact.isClosed.isOpen_compl.preimage continuous_fst)
        (L.isCompact.isClosed.isOpen_compl.preimage continuous_snd) p q
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (TopCat.prodFst : TopCat.of (X×Y) ⟶ X)
          (A := Prod.fst ⁻¹' (K : Set X)ᶜ) (B := (K : Set X)ᶜ)
          (fun _ hx => hx) p a) b))

theorem compactFirstFactorSupportedCup_eq_stage (x : X)
    (H : ContinuousMap.Homotopy (ContinuousMap.const X x) (ContinuousMap.id X))
    (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (Prod.snd ⁻¹' (L : Set Y)ᶜ) q) :
    compactFirstFactorSupportedCup X Y K L p q a b =
    CompactExteriorCup.Constructions.compactExteriorCupStage X Y K L p q a
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X Y x) (A := (L : Set Y)ᶜ)
        (B := Prod.snd ⁻¹' (L : Set Y)ᶜ) (fun _ hx => hx) q b) := by
  unfold compactFirstFactorSupportedCup
  rw [supportedFirstFactorCup_eq_exterior X Y x H _ _
    K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedProductTest.Constructions
