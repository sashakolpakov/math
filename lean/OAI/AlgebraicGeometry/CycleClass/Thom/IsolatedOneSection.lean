import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionNonzero
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorOneStep
import OAI.AlgebraicGeometry.CycleClass.Thom.PointConcentration

/-! # Isolated One Section -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection.Constructions.Class

noncomputable section

/-! Complete local one-equation class formula: the actual cycle-vector
class near the target generic point is its original target cycle with
the native Tor Euler coefficient. Nonvanishing is derived from isolation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionNonzero.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerEmpty.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorOneStep.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PointConcentration.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier))
  (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B)

include hc hxB in
theorem sourceNonempty (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0) :
    Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B) :=
  Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty D B (IntersectionGeometry.supportPoint Z.val) (hc D hD) hxB

variable (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))

local notation "x" => OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val
local notation "R" => V.carrier.presheaf.stalk (OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val)
local notation "t" => V.carrier.presheaf.germ B (OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val) hxB (B.topIso.hom r)

variable (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
  PrimeSpectrum.zeroLocus
    (Ideal.ofList [V.carrier.presheaf.germ B (IntersectionGeometry.supportPoint Z.val) hxB (B.topIso.hom r)] :
      Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))) ∩
    Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
      (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val (IntersectionGeometry.supportPoint Z.val) (hc D hD)) ⊆
        {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))})

include hi in
theorem sectionNonzero (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0) :
    letI := sourceNonempty V p Z c hc B hxB D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B r ≠ 0 := by
  let := sourceNonempty V p Z c hc B hxB D hD
  exact IsolatedSectionNonzero.Constructions.parentFunction_ne_zero V p (p + 1) D Z (Nat.lt_succ_self p) (hc D hD) B hxB r (hi D hD)

local notation "hne" => OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection.Constructions.Class.sourceNonempty V p Z c hc B hxB
local notation "hs" => OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection.Constructions.Class.sectionNonzero V p Z c hc B hxB r hi

def oneSectionStep : Geometric.DimensionCycles.RationalDimensionCycle V (p + 1) := Finite.SectionEuler.Constructions.originalPrincipalStepSum V p B r c hne hs

local notation "c₁" => OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection.Constructions.Class.oneSectionStep V p Z c hc B hxB r hi

theorem oneSectionStep_coefficient (hr : IsWeaklyRegular R [t])
    (hm : ∀ a ∈ [t], a ∈ IsLocalRing.maximalIdeal R) (l : ℕ) :
    c₁ Z = Local.Euler.Constructions.localCycleEuler V p x [t] l c := by
  have he := Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum.localCycleEuler_step V p B r c hne hs x hxB [] hr hm (fun D hD _ => hi D hD) l (Nat.zero_le l)
  exact (he.trans (Local.EulerEmpty.Constructions.localCycleEuler_empty V (p + 1) Z c₁ l)).symm

variable [Nonempty B]

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ)
  (hcu : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)

local notation "s" => (fun _ : Fin 1 => r)
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class.vectorIntersectionSupport V B U hU u 1 s

include hcu in
theorem oneSectionStep_supported (D : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hD : c₁ D ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S := by
  have hd : Finite.CycleSectionClass.Constructions.cycleSectionStep V p B r U u c hcu hne hs D ≠ 0 := by
    rw [Finite.SectionEuler.Constructions.cycleSectionStep_eq_sum]
    exact hD
  have h := Finite.CycleSectionClass.Constructions.cycleSectionStep_supported V p B r U hU u c hcu hne hs D hd
  change (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆
    Set.range u ∩ Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU 1 s)
  rw [BaseVectorNormal.Constructions.Class.vectorZeroImage_one]
  exact h

include hcu in
theorem cycleVectorClass_singleEuler (hr : IsWeaklyRegular R [t])
    (hm : ∀ a ∈ [t], a ∈ IsLocalRing.maximalIdeal R) (l : ℕ)
    (hPoint : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver (Cycle.AtPoint.Constructions.pointNeighborhood V (p + 1) x c₁ B)) :
    Cycle.Vector.Constructions.Class.cycleVectorClassAt V B U hU u p 1 (p + 1) rfl s hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1)
        (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (Finsupp.single Z (Local.Euler.Constructions.localCycleEuler V p x [t] l c))) := by
  have hbase := Cycle.VectorOneStep.Constructions.cycleVectorClass_one V p B r U hU u hu c hcu hne hs
  have hconc := PointConcentration.Constructions.relativeClass_eq_single_near_generic V (p + 1) Z c₁ B U hPoint S
    (oneSectionStep_supported V p Z c hc B hxB r hi U hU u hcu)
  have hcoef := oneSectionStep_coefficient V p Z c hc B hxB r hi hr hm l
  exact hbase.trans (hconc.trans (congrArg (fun a : ℚ =>
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1) (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (Finsupp.single Z a))) hcoef))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection.Constructions.Class
