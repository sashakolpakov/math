import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorPrincipal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

/-! # Cycle Maps -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps

noncomputable section

/-! Native restriction and embedding of finite cycles along an open and
closed immersion. Divisor restriction is the actual smooth inverse image. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
  (m : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

def embed (p : ℕ) : V.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle p :=
  Finsupp.lmapDomain ℚ ℚ (Cycle.supportImage i m p)

def restrict (p : ℕ) : X.RationalDimensionCycle p →ₗ[ℚ] V.RationalDimensionCycle p :=
  Finsupp.lcomapDomain (Cycle.supportImage i m p) (Cycle.supportImage_injective i m p)

theorem restrict_apply (p : ℕ) (a : X.RationalDimensionCycle p) (A : V.DimensionCycleSupport p) :
    restrict i m p a A = a (Cycle.supportImage i m p A) := rfl

theorem embed_single (p : ℕ) (A : V.DimensionCycleSupport p) (r : ℚ) :
    embed i m p (Finsupp.single A r) = Finsupp.single (Cycle.supportImage i m p A) r := Finsupp.mapDomain_single

theorem restrict_embed (p : ℕ) (a : V.RationalDimensionCycle p) : restrict i m p (embed i m p a) = a :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ (Cycle.supportImage_injective i m p) a

theorem embed_eq_pushforward (p : ℕ) : embed i m p = ProperCycleLinearity.cyclePushforward i p p := by
  apply Finsupp.lhom_ext
  intro A r
  rw [embed_single, ProperCycleLinearity.cyclePushforward_single, ProperCycleLinearity.cyclePushforwardGenerator,
    Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, one_smul,
    CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left ((Cycle.image_codimension i m A.val).trans A.property)]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem flatMap_eq_restrict (a : X.RationalDimensionCycle 1) : CurveFiberCycle.flatMap i a = restrict i m 1 a := by
  ext A
  exact Smooth.DivisorPrincipal.flatMap_apply_at_point i m m a A (Cycle.supportImage i m 1 A)
    (Cycle.image_point i A.val).symm

theorem embed_restrict (p : ℕ) (a : X.RationalDimensionCycle p)
    (ha : ∀ A ∈ a.support, (A.val : Set X.carrier) ⊆ Set.range i.left) : embed i m p (restrict i m p a) = a := by
  apply Finsupp.mapDomain_comapDomain _ (Cycle.supportImage_injective i m p)
  intro A hA
  exact ⟨Cycle.supportPreimage i m p A (ha A hA), Cycle.supportImage_preimage i m p A (ha A hA)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps
