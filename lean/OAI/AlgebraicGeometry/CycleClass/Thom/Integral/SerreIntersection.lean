import OAI.AlgebraicGeometry.CycleClass.Thom.PositiveSerreIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.ZeroCodimensionSerre

/-! # Serre Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SerreIntersection.Constructions

noncomputable section

/-! The actual proper Serre intersection of any two supports on an
integral smooth projective variety maps to the original cup product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ZeroCodimensionSerre.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (hproper : ∀ Z : IrreducibleCloseds V.carrier,
    (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z)

theorem geometricClass_supportedSerreCycle :
    V.geometricCycleClassMap (p + q)
      (Supported.Map.Constructions.forgetCycle V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper)) =
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (p + p) (q + q)
        A.geometricCycleClass B.geometricCycleClass) := by
  by_cases hv : 0 < V.complexDimension
  · exact PositiveSerreIntersection.Constructions.geometricClass_supportedSerreCycle V p q A B hproper hv
  · have hdim : V.complexDimension = 0 := by omega
    have hp : p = 0 := by
      have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V A.val
      rw [A.property] at h
      have hd := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension V
      omega
    have hq : q = 0 := by
      have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V B.val
      rw [B.property] at h
      have hd := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension V
      omega
    subst p
    subst q
    have he : A = B := by
      apply Subtype.ext
      apply IrreducibleCloseds.ext
      exact (ZeroCodimensionSerre.Constructions.support_univ V A).trans (ZeroCodimensionSerre.Constructions.support_univ V B).symm
    subst B
    exact ZeroCodimensionSerre.Constructions.geometricClass_selfSerre V A hproper

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SerreIntersection.Constructions
