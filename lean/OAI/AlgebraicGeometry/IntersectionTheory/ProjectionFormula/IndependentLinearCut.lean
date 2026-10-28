import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ConstrainedLinearForms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Independent Linear Cut -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentLinearCut

noncomputable section

/-! The linear coordinate-cutting construction can simultaneously
produce independent images under finitely many surjective linear maps.
This separates the geometric cutting from the later tangent-space choices. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  {ι : Type} [Finite ι]
  (D : ι → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
  (hD : ∀ j, Function.Surjective (D j))

include m in
theorem codimension_cons (k : ℕ)
    (L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hcodim : ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a => (L a).val) → k ≤ X.supportCodimension W)
    (p : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hp : ∀ C : irreducibleComponents (Projective.LinearCut.commonZero X.embedding (fun a => (L a).val)),
      p.val ∉ (X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier
        (Projective.LinearCut.commonZero X.embedding (fun a => (L a).val)) C))).asHomogeneousIdeal) :
    ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a : Fin (k + 1) => (Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) p L a).val) →
      k + 1 ≤ X.supportCodimension W := by
  let S := Projective.LinearCut.commonZero X.embedding (fun a => (L a).val)
  intro W hW
  have hWS : (W : Set X.carrier) ⊆ S := by
    intro x hx
    apply (Projective.LinearCut.mem_commonZero X.embedding (fun a => (L a).val) x).mpr
    intro a
    exact (Projective.LinearCut.mem_commonZero X.embedding (fun a : Fin (k + 1) => (Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) p L a).val) x).mp (hW hx) a.succ
  obtain ⟨C, hC⟩ := Supports.closedComponentSupport_covers X.carrier S W hWS
  have hne : W ≠ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C := by
    intro he
    have hx : CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C) ∈ (W : Set X.carrier) :=
      he ▸ (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
    exact hp C ((Projective.LinearCut.mem_commonZero X.embedding (fun a : Fin (k + 1) => (Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) p L a).val) _).mp (hW hx) 0)
  have hlt := Supports.codimension_strictAnti X m (lt_of_le_of_ne hC hne)
  have hb := hcodim (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C) (Supports.closedComponentSupport_subset X.carrier S C)
  omega

omit [SmoothOfRelativeDimension m X.structureMap] [Finite ι] in
include hD in
theorem comap_span_ne_top {k : ℕ} (hk : k < m + 1)
    (L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hLI : ∀ j, LinearIndependent ℂ (fun a => D j (L a))) (j : ι) :
    (Submodule.span ℂ (Set.range (fun a => D j (L a)))).comap (D j) ≠ ⊤ := by
  let T := Submodule.span ℂ (Set.range (fun a => D j (L a)))
  have hT : T ≠ ⊤ := by
    intro he
    have hr := finrank_span_eq_card (hLI j)
    change Module.finrank ℂ T = Fintype.card (Fin k) at hr
    rw [he, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at hr
    omega
  intro he
  apply hT
  apply top_unique
  intro w _
  obtain ⟨a, rfl⟩ := hD j w
  have ha : a ∈ T.comap (D j) := by rw [he]; trivial
  exact ha

include hD in
theorem exists_partial (k : ℕ) (hk : k ≤ m + 1) :
    ∃ L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ W : IrreducibleCloseds X.carrier,
        (W : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a => (L a).val) → k ≤ X.supportCodimension W) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, fun _ _ => Nat.zero_le _, fun _ => linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨L, hcodim, hLI⟩ := ih (by omega)
    let S := Projective.LinearCut.commonZero X.embedding (fun a => (L a).val)
    let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
    let : Finite (irreducibleComponents S) :=
      (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
    let T (j : ι) := Submodule.span ℂ (Set.range (fun a => D j (L a)))
    let N (j : ι) := (T j).comap (D j)
    have hN (j : ι) : N j ≠ ⊤ := by
      exact comap_span_ne_top X m D hD (by omega) L hLI j
    obtain ⟨p, hp, hpN⟩ := ConstrainedLinearForms.exists_form X.ambientDimension
      (fun C : irreducibleComponents S => X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S C))) N hN
    refine ⟨Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) p L, ?_, ?_⟩
    · exact codimension_cons X m k L hcodim p hp
    · intro j
      have heq : (fun a : Fin (k + 1) => D j (Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) p L a)) = Fin.cons (α := fun _ => Fin (m + 1) → ℂ) (D j p) (fun a => D j (L a)) := by
        funext a
        exact Fin.cases rfl (fun _ => rfl) a
      rw [heq, linearIndependent_finCons]
      exact ⟨hLI j, hpN j⟩

include hD in
theorem exists_full :
    ∃ L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  obtain ⟨L, hcodim, hLI⟩ := exists_partial X m D hD (m + 1) le_rfl
  refine ⟨L, ?_, hLI⟩
  intro x
  by_contra hn
  push Not at hn
  let W : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm x
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint W = x := irreducibleSetEquivPoints.apply_symm_apply x
  have hW : (W : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a => (L a).val) := by
    apply (Supports.supportPoint_mem_iff_subset (Projective.LinearCut.commonZero X.embedding (fun a => (L a).val)) W).mp
    rw [hp]
    exact (Projective.LinearCut.mem_commonZero X.embedding (fun a => (L a).val) x).mpr hn
  have hl := hcodim W hW
  have hd := Grading.supportDimension_add_codimension X m W
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentLinearCut
