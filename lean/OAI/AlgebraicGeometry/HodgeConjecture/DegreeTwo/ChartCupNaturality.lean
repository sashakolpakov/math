import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartTangentPullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupNaturality

/-! # Chart Cup Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartCupNaturality.Constructions

noncomputable section

/-!
# DegreeTwo: supported cup compatibility for general changes of product coordinates

The transition may mix the coordinates. Its literal zero-section map and
preservation of the actual normal class imply compatibility in every degree.
Both support conditions are retained explicitly.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem relativeExteriorCup_chart_naturality
    {X X' Y Y' : TopCat.{0}} (f : TopCat.of (X×Y) ⟶ TopCat.of (X'×Y')) (g : Y ⟶ Y')
    (x : X) (x' : X')
    (H : ContinuousMap.Homotopy (ContinuousMap.const X x) (ContinuousMap.id X))
    (hsec : CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X Y x ≫ f = g ≫ CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X' Y' x')
    (A : Set X) (A' : Set X') (B : Set Y) (B' : Set Y')
    (hA : IsOpen A) (hA' : IsOpen A') (hB : IsOpen B) (hB' : IsOpen B')
    (hfA : Set.MapsTo f (Prod.fst ⁻¹' A) (Prod.fst ⁻¹' A'))
    (hfB : Set.MapsTo f (Prod.snd ⁻¹' B) (Prod.snd ⁻¹' B'))
    (hg : Set.MapsTo g B B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (a' : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X' A' p)
    (hnormal : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hfA p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X'×Y') ⟶ X') (A := Prod.fst ⁻¹' A') (B := A')
        (fun _ hx => hx) p a') =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X×Y) ⟶ X) (A := Prod.fst ⁻¹' A) (B := A)
        (fun _ hx => hx) p a)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' B' q) :
    ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (hfA.union_union hfB) (p+q)
      (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X' Y' A' B' hA' hB' p q a' b) := by
  have ht := ChartTangentPullback.Constructions.chartTangent_relativePullback f g x x' hfB hg hsec H q b
  have hc := SupportCup.Constructions.twoSupportCohomologyCup_naturality (TopCat.of (X×Y))
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
    (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q f
    (Prod.fst ⁻¹' A') (Prod.snd ⁻¹' B')
    (hA'.preimage continuous_fst) (hB'.preimage continuous_snd) hfA hfB
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (TopCat.prodFst : TopCat.of (X'×Y') ⟶ X') (A := Prod.fst ⁻¹' A') (B := A')
      (fun _ hx => hx) p a')
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection X' Y') (A := Prod.snd ⁻¹' B') (B := B')
      (fun _ hx => hx) q b)
  have hl := congrArg₂
    (fun u v => SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
      (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q u v) hnormal ht
  exact hl.symm.trans hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartCupNaturality.Constructions
