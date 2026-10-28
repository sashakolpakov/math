import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductSupportRetraction

/-! # Chart Tangent Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartTangentPullback.Constructions

noncomputable section

/-!
# DegreeTwo: tangential support under a map between product neighborhoods

The map may mix normal and tangent coordinates. A genuine normal contraction
and the literal equality on the zero sections identify its relative pullback.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable {X X' Y Y' : TopCat.{0}}
variable (f : TopCat.of (X×Y) ⟶ TopCat.of (X'×Y')) (g : Y ⟶ Y') (x : X) (x' : X')
variable {B : Set Y} {B' : Set Y'}
variable (hf : Set.MapsTo f (Prod.snd ⁻¹' B) (Prod.snd ⁻¹' B')) (hg : Set.MapsTo g B B')
variable (hsec : CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X Y x ≫ f = g ≫ CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X' Y' x')

include hsec in
theorem chartSection_relativePullback (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X'×Y')) (Prod.snd ⁻¹' B') q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X Y x)
      (A := B) (B := Prod.snd ⁻¹' B) (fun _ hx => hx) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X' Y' x')
        (A := B') (B := Prod.snd ⁻¹' B') (fun _ hx => hx) q b) := by
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf q ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X Y x)
      (A := B) (B := Prod.snd ⁻¹' B) (fun _ hx => hx) q) b =
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X' Y' x')
      (A := B') (B := Prod.snd ⁻¹' B') (fun _ hx => hx) q ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q) b
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  congr 2
  congr 1

include hsec in
theorem chartTangent_relativePullback
    (H : ContinuousMap.Homotopy (ContinuousMap.const X x) (ContinuousMap.id X)) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' B' q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection X' Y')
        (A := Prod.snd ⁻¹' B') (B := B') (fun _ hx => hx) q a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection X Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q a) := by
  let b := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection X' Y')
    (A := Prod.snd ⁻¹' B') (B := B') (fun _ hx => hx) q a
  have hr := ProductSupportRetraction.Constructions.secondSupport_class_eq_pullback X Y (ModuleCat.of ℚ ℚ) x H B q
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf q b)
  have hs := chartSection_relativePullback f g x x' hf hg hsec q b
  have hi : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X' Y' x')
      (A := B') (B := Prod.snd ⁻¹' B') (fun _ hx => hx) q b = a := by
    change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection X' Y')
      (A := Prod.snd ⁻¹' B') (B := B') (fun _ hx => hx) q ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection X' Y' x')
      (A := B') (B := Prod.snd ⁻¹' B') (fun _ hx => hx) q) a = a
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Y') (fun _ hx => hx) q a = a
    rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, ModuleCat.id_apply]
  have hs' := hs.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q) hi)
  exact hr.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection X Y) (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q) hs')

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartTangentPullback.Constructions
