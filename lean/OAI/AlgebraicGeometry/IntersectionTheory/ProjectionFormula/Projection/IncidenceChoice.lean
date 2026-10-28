import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IncidenceComponentConstraint
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairIncidenceStep

/-! # Incidence Choice -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.IncidenceChoice

noncomputable section

/-! One new projection coordinate simultaneously cuts all factor
base loci and pair incidences and extends the prescribed independent jets. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

theorem exists_form (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ) (hk : k < m)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (D : ι → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
    (hD : ∀ j, Function.Surjective (D j))
    (hLI : ∀ j, LinearIndependent ℂ (fun a => D j (L a))) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ C : irreducibleComponents (Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)),
        a.val ∉ (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier
          (Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)) C))).asHomogeneousIdeal) ∧
      (∀ t, ∀ C : irreducibleComponents (Support.PairBase.factor X (W t) L),
        a.val ∉ ((CycleClass.Geometric.GenericPoint.reducedSupportι (W t) ≫ X.embedding) (CycleClass.Thom.IntersectionGeometry.supportPoint
          (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (CycleClass.Geometric.GenericPoint.reducedSupportScheme (W t)) (Support.PairBase.factor X (W t) L) C))).asHomogeneousIdeal) ∧
      (∀ t, ∀ C : irreducibleComponents (Support.PairBase.factor X (Z t) L),
        a.val ∉ ((CycleClass.Geometric.GenericPoint.reducedSupportι (Z t) ≫ X.embedding) (CycleClass.Thom.IntersectionGeometry.supportPoint
          (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (CycleClass.Geometric.GenericPoint.reducedSupportScheme (Z t)) (Support.PairBase.factor X (Z t) L) C))).asHomogeneousIdeal) ∧
      (∀ j, D j a ∉ Submodule.span ℂ (Set.range (fun b => D j (L b)))) ∧
      ∀ t, ∀ C : irreducibleComponents (Support.PairIncidenceStep.incidence X (W t) (Z t) k L),
        ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (Support.Pair.space X (W t) (Z t))
          (Support.PairIncidenceStep.incidence X (W t) (Z t) k L) C : Set (Support.Pair.space X (W t) (Z t))) ⊆
          Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport (Support.Pair.space X (W t) (Z t))
          (Support.PairIncidenceStep.incidence X (W t) (Z t) k L) C,
          x ∉ Support.PairIncidenceStep.incidence X (W t) (Z t) (k + 1) (Fin.cons a L) := by
  classical
  let S := Projective.LinearCut.commonZero X.embedding (fun b => (L b).val)
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  let H : τ ⊕ τ → IrreducibleCloseds X.carrier := Sum.elim W Z
  let B t := Support.PairBase.factor X (H t) L
  let (t : τ ⊕ τ) : NoetherianSpace (B t) := NoetherianSpace.set (B t : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme (H t)))
  let (t : τ ⊕ τ) : Finite (irreducibleComponents (B t)) :=
    (NoetherianSpace.finite_irreducibleComponents (α := B t)).to_subtype
  let z : irreducibleComponents S ⊕ (Σ t : τ ⊕ τ, irreducibleComponents (B t)) →
      Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension := Sum.elim
    (fun C => X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C)))
    (fun b => (CycleClass.Geometric.GenericPoint.reducedSupportι (H b.1) ≫ X.embedding)
      (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (CycleClass.Geometric.GenericPoint.reducedSupportScheme (H b.1)) (B b.1) b.2)))
  let N j := (Submodule.span ℂ (Set.range (fun b => D j (L b)))).comap (D j)
  have hN : ∀ j, N j ≠ ⊤ :=
    fun j => IndependentLinearCut.comap_span_ne_top X m D hD (by omega) L hLI j
  obtain ⟨a, ha, haN, haI⟩ := IncidenceComponentConstraint.FamilyCut.exists_form X k L
    (fun t => Support.Pair.over X (W t) (Z t)) (fun t => Support.Pair.first X (W t) (Z t))
    (fun t => Support.Pair.second X (W t) (Z t)) z N hN
  exact ⟨a, fun C => ha (Sum.inl C),
    fun t C => ha (Sum.inr ⟨Sum.inl t, C⟩), fun t C => ha (Sum.inr ⟨Sum.inr t, C⟩),
    fun j => haN j, haI⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.IncidenceChoice
