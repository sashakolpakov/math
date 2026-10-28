import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CutAwayFromPoint

/-! # Simultaneous Fiber Cut -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousFiberCut

noncomputable section

/-! A single degree-one form cuts finitely many fibers properly away
from their designated points while extending prescribed independent jets. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

theorem finite_components (S : Closeds X.carrier) : Finite (irreducibleComponents S) := by
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  exact (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype

theorem exists_form (m : ℕ) {ι κ : Type} [Finite ι] [Finite κ]
    (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)) (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _)
    (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hs : ∀ j, PointFiberLinearForms.value X (p j) (hp j) s ≠ 0)
    (S : ι → Closeds X.carrier) (T : Closeds X.carrier)
    (D : κ → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
    (hD : ∀ j, Function.Surjective (D j))
    {k : ℕ} (hk : k < m + 1) (L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hLI : ∀ j, LinearIndependent ℂ (fun a => D j (L a))) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ C : irreducibleComponents T,
        a.val ∉ (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier T C))).asHomogeneousIdeal) ∧
      (∀ j, ∀ C : irreducibleComponents (S j),
        ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S j) C : Set X.carrier) ⊆
          {p j (IsLocalRing.closedPoint ℂ)} →
        ∃ y : X.carrier, y ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S j) C ∧
          (PointFiberLinearForms.cross X (p j) (hp j) s a).val ∉ (X.embedding y).asHomogeneousIdeal) ∧
      ∀ j, D j a ∉ Submodule.span ℂ (Set.range (fun b => D j (L b))) := by
  classical
  let : Finite (irreducibleComponents T) := finite_components X T
  let (j : ι) : Finite (irreducibleComponents (S j)) := finite_components X (S j)
  let B := Σ j : ι, {C : irreducibleComponents (S j) //
    ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S j) C : Set X.carrier) ⊆
      {p j (IsLocalRing.closedPoint ℂ)}}
  have hw (b : B) : ∃ y : X.carrier,
      y ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S b.1) b.2.val ∧
      y ≠ p b.1 (IsLocalRing.closedPoint ℂ) ∧ IsClosed ({y} : Set _) :=
    CutAwayFromPoint.closed_witness X _
      (((pointEquivClosedPoint X.structureMap) ⟨p b.1, hp b.1⟩).property) _ b.2.property
  choose y hy hyne hyclosed using hw
  let N : B ⊕ κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :=
    Sum.elim
      (fun b => (ConstrainedLinearForms.pointSubmodule X.ambientDimension
        (X.embedding (y b))).comap (PointFiberLinearForms.cross X (p b.1) (hp b.1) s))
      (fun j => (Submodule.span ℂ (Set.range (fun b => D j (L b)))).comap (D j))
  have hN : ∀ b, N b ≠ ⊤ := by
    intro b
    cases b with
    | inl b =>
      exact PointFiberLinearForms.constraint_ne_top X (p b.1) (hp b.1) s (hs b.1) (y b) (hyclosed b) (hyne b)
    | inr j => exact IndependentLinearCut.comap_span_ne_top X m D hD hk L hLI j
  obtain ⟨a, ha, haN⟩ := ConstrainedLinearForms.exists_form X.ambientDimension
    (fun C : irreducibleComponents T =>
      X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier T C))) N hN
  refine ⟨a, ha, ?_, fun j => haN (Sum.inr j)⟩
  intro j C hC
  let b : B := ⟨j, C, hC⟩
  exact ⟨y b, hy b, haN (Sum.inl b)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousFiberCut
