import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousFiberCut

/-! # Fiber Cut Induction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberCutInduction

noncomputable section

section

/-! Iterated simultaneous fiber cuts produce base-point-free linear
coordinates with independent jets and singleton fibers on lower-dimensional supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

theorem commonZero_cons {X : Scheme} {n k : ℕ} (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (a : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) (L : Fin k → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) :
    Projective.LinearCut.commonZero i (Fin.cons a L) = Projective.LinearCut.commonZero i L ⊓ Projective.LinearCut.zeroSet i a := by
  ext x
  change x ∈ Projective.LinearCut.commonZero i (Fin.cons a L) ↔ x ∈ Projective.LinearCut.commonZero i L ⊓ Projective.LinearCut.zeroSet i a
  rw [Projective.LinearCut.mem_commonZero]
  change (∀ j, Fin.cons (α := fun _ => Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) a L j ∈ (i x).asHomogeneousIdeal) ↔
    x ∈ Projective.LinearCut.commonZero i L ∧ ¬ a ∉ (i x).asHomogeneousIdeal
  rw [Projective.LinearCut.mem_commonZero, not_not, Fin.forall_fin_succ]
  exact and_comm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]
  {ι κ : Type} [Finite ι] [Finite κ]
  (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)) (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _)
  (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (hs : ∀ j, PointFiberLinearForms.value X (p j) (hp j) s ≠ 0)
  (hscut : ∀ W : IrreducibleCloseds X.carrier,
    (W : Set X.carrier) ⊆ Projective.LinearCut.zeroSet X.embedding s.val → 1 ≤ X.supportCodimension W)
  (Z : ι → Closeds X.carrier)
  (hZ : ∀ j, ∀ W : IrreducibleCloseds X.carrier,
    (W : Set X.carrier) ⊆ Z j → 1 ≤ X.supportCodimension W)
  (D : κ → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
  (hD : ∀ j, Function.Surjective (D j)) (hDs : ∀ j, D j s ≠ 0)

include hs hscut hZ hD hDs in
theorem exists_partial (k : ℕ) (hk : k ≤ m) :
    ∃ L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      s ∈ Set.range L ∧
      (∀ W : IrreducibleCloseds X.carrier,
        (W : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a => (L a).val) →
          k + 1 ≤ X.supportCodimension W) ∧
      (∀ j, ∀ W : IrreducibleCloseds X.carrier,
        (W : Set X.carrier) ⊆ Z j ⊓ Projective.LinearCut.commonZero X.embedding
          (fun a => (PointFiberLinearForms.cross X (p j) (hp j) s (L a)).val) →
        ¬ (W : Set X.carrier) ⊆ {p j (IsLocalRing.closedPoint ℂ)} →
          k + 1 ≤ X.supportCodimension W) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  induction k with
  | zero =>
    refine ⟨fun _ => s, ⟨0, rfl⟩, ?_, ?_, ?_⟩
    · intro W hW
      apply hscut W
      intro x hx
      change ¬ s.val ∉ (X.embedding x).asHomogeneousIdeal
      exact not_not.mpr ((Projective.LinearCut.mem_commonZero X.embedding (fun _ : Fin 1 => s.val) x).mp (hW hx) 0)
    · intro j W hW _
      exact hZ j W (fun x hx => (hW hx).1)
    · intro j
      change LinearIndependent ℂ (fun _ : Fin 1 => D j s)
      exact linearIndependent_unique_iff.mpr (hDs j)
  | succ k ih =>
    obtain ⟨L, hLs, hcodim, hfiber, hLI⟩ := ih (by omega)
    let T := Projective.LinearCut.commonZero X.embedding (fun a => (L a).val)
    let S j := Z j ⊓ Projective.LinearCut.commonZero X.embedding (fun a => (PointFiberLinearForms.cross X (p j) (hp j) s (L a)).val)
    obtain ⟨a, ha, haf, haD⟩ := SimultaneousFiberCut.exists_form X m p hp s hs S T
      D hD (by omega) L hLI
    let L' : Fin (k + 1 + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 := Fin.cons a L
    have hT : Projective.LinearCut.commonZero X.embedding (fun b => (L' b).val) = T ⊓ Projective.LinearCut.zeroSet X.embedding a.val := by
      rw [show (fun b => (L' b).val) = Fin.cons a.val (fun b => (L b).val) from by
        funext b; exact Fin.cases rfl (fun _ => rfl) b]
      exact commonZero_cons X.embedding a.val (fun b => (L b).val)
    have hS (j : ι) : Z j ⊓ Projective.LinearCut.commonZero X.embedding
        (fun b => (PointFiberLinearForms.cross X (p j) (hp j) s (L' b)).val) =
        S j ⊓ Projective.LinearCut.zeroSet X.embedding (PointFiberLinearForms.cross X (p j) (hp j) s a).val := by
      rw [show (fun b => (PointFiberLinearForms.cross X (p j) (hp j) s (L' b)).val) =
        Fin.cons (PointFiberLinearForms.cross X (p j) (hp j) s a).val
          (fun b => (PointFiberLinearForms.cross X (p j) (hp j) s (L b)).val) from by
            funext b; exact Fin.cases rfl (fun _ => rfl) b]
      rw [commonZero_cons, ← inf_assoc]
    refine ⟨L', ?_, ?_, ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hLs
      exact ⟨b.succ, hb⟩
    · rw [hT]
      exact CutAwayFromPoint.cut_all X m (k + 1) T hcodim a.val ha
    · intro j
      change ∀ W : IrreducibleCloseds X.carrier,
        (W : Set X.carrier) ⊆ (Z j ⊓ Projective.LinearCut.commonZero X.embedding
          (fun b => (PointFiberLinearForms.cross X (p j) (hp j) s (L' b)).val) : Closeds X.carrier) →
        ¬ (W : Set X.carrier) ⊆ {p j (IsLocalRing.closedPoint ℂ)} →
          k + 1 + 1 ≤ X.supportCodimension W
      rw [hS]
      exact CutAwayFromPoint.cut X m (k + 1) (p j (IsLocalRing.closedPoint ℂ))
        (S j) (hfiber j) (PointFiberLinearForms.cross X (p j) (hp j) s a).val (haf j)
    · intro j
      have he : (fun b => D j (L' b)) = Fin.cons (D j a) (fun b => D j (L b)) := by
        funext b
        exact Fin.cases rfl (fun _ => rfl) b
      rw [he, linearIndependent_finCons]
      exact ⟨hLI j, haD j⟩

end

/-! Unconditional simultaneous choices of linear forms with independent
first-order data and isolated fibers on positive-codimension supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace SeparatingForms

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]
  {ι κ : Type} [Finite ι] [Finite κ]
  (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)) (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _)
  (D : κ → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] (Fin (m + 1) → ℂ))
  (hD : ∀ j, Function.Surjective (D j))

include hD m in
theorem initial : ∃ s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
    (∀ j, PointFiberLinearForms.value X (p j) (hp j) s ≠ 0) ∧
    (∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ Projective.LinearCut.zeroSet X.embedding s.val → 1 ≤ X.supportCodimension W) ∧
    ∀ j, D j s ≠ 0 := by
  let T : Closeds X.carrier := ⊤
  let : Finite (irreducibleComponents T) := SimultaneousFiberCut.finite_components X T
  let N j : Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :=
    (⊥ : Submodule ℂ (Fin (m + 1) → ℂ)).comap (D j)
  have hN : ∀ j, N j ≠ ⊤ := by
    intro j
    have h := IndependentLinearCut.comap_span_ne_top X m D hD (Nat.zero_lt_succ m)
      (Fin.elim0 : Fin 0 → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (fun _ => linearIndependent_empty_type) j
    simpa only [Set.range_eq_empty, Submodule.span_empty] using h
  let q : irreducibleComponents T ⊕ ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension :=
    Sum.elim (fun C => X.embedding (CycleClass.Thom.IntersectionGeometry.supportPoint (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier T C)))
      (fun j => X.embedding (p j (IsLocalRing.closedPoint ℂ)))
  obtain ⟨s, hs, hsN⟩ := ConstrainedLinearForms.exists_form X.ambientDimension q N hN
  refine ⟨s, ?_, ?_, fun j => hsN j⟩
  · intro j
    exact fun h => hs (Sum.inr j) ((PointFiberLinearForms.value_zero X (p j) (hp j) s).mp h)
  · intro W hW
    exact CutAwayFromPoint.cut_all X m 0 T (fun _ _ => Nat.zero_le _) s.val
      (fun C => hs (Sum.inl C)) W (fun x hx => ⟨Set.mem_univ _, hW hx⟩)

include hD m in
theorem exists_forms (Z : ι → Closeds X.carrier)
    (hZ : ∀ j, ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ Z j → 1 ≤ X.supportCodimension W) :
    ∃ (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1),
      s ∈ Set.range L ∧ (∀ j, PointFiberLinearForms.value X (p j) (hp j) s ≠ 0) ∧
      (∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal) ∧
      (∀ j, (Z j ⊓ Projective.LinearCut.commonZero X.embedding
        (fun a => (PointFiberLinearForms.cross X (p j) (hp j) s (L a)).val) : Set X.carrier) ⊆
          {p j (IsLocalRing.closedPoint ℂ)}) ∧
      ∀ j, LinearIndependent ℂ (fun a => D j (L a)) := by
  obtain ⟨s, hs, hscut, hDs⟩ := initial X m p hp D hD
  obtain ⟨L, hLs, hcodim, hfiber, hLI⟩ :=
    exists_partial X m p hp s hs hscut Z hZ D hD hDs m le_rfl
  refine ⟨s, L, hLs, hs, ?_, ?_, hLI⟩
  · intro x
    by_contra hn
    push Not at hn
    let W : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm x
    have hpW : CycleClass.Thom.IntersectionGeometry.supportPoint W = x := irreducibleSetEquivPoints.apply_symm_apply x
    have hW : (W : Set X.carrier) ⊆ Projective.LinearCut.commonZero X.embedding (fun a => (L a).val) := by
      apply (Supports.supportPoint_mem_iff_subset _ W).mp
      rw [hpW]
      exact (Projective.LinearCut.mem_commonZero X.embedding (fun a => (L a).val) x).mpr hn
    have hb := hcodim W hW
    have hd := Grading.supportDimension_add_codimension X m W
    omega
  · intro j
    exact CutAwayFromPoint.subset_singleton X m
      (Z j ⊓ Projective.LinearCut.commonZero X.embedding (fun a => (PointFiberLinearForms.cross X (p j) (hp j) s (L a)).val))
      (p j (IsLocalRing.closedPoint ℂ)) (hfiber j)

end SeparatingForms

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberCutInduction
