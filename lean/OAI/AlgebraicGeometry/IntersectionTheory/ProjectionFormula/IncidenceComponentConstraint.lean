import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousIncidenceCut

/-! # Incidence Component Constraint -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IncidenceComponentConstraint

noncomputable section

section

/-! Each non-diagonal coincidence component supplies one proper
linear subspace to avoid in the next coordinate choice. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

theorem exists_submodule (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [NoetherianSpace T.left] [LocallyOfFiniteType T.hom]
    (u v : T ⟶ X.toOver) (C : irreducibleComponents (Projection.Coincidence.locus X k L u v))
    (hC : ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport T.left (Projection.Coincidence.locus X k L u v) C : Set T.left) ⊆
      Closed.Equalizer.locus u v) :
    ∃ N : Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1), N ≠ ⊤ ∧
      ∀ a ∉ N, ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport T.left (Projection.Coincidence.locus X k L u v) C,
        x ∉ Projection.Coincidence.locus X (k + 1) (Fin.cons a L) u v := by
  let U := Projection.Coincidence.domain X k L u v
  let A := CoincidenceClosedPointTest.OpenClosure.openLocus U (Projection.Coincidence.first X k L u v) (Projection.Coincidence.second X k L u v)
  obtain ⟨x, hxC, hxU, hxF, hxc⟩ := ClosedDifferenceDimension.ClosureComponentWitness.closed_witness
    T.hom U A (Closed.Equalizer.locus u v) C hC
  let p := pointOfClosedPoint T.hom x hxc
  have hp : p ≫ T.hom = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let p₁ := p ≫ u.left
  let p₂ := p ≫ v.left
  have hp₁ : p₁ ≫ X.structureMap = 𝟙 _ := CoincidenceExtension.point_over X u p hp
  have hp₂ : p₂ ≫ X.structureMap = 𝟙 _ := CoincidenceExtension.point_over X v p hp
  have hne : p₁ (IsLocalRing.closedPoint ℂ) ≠ p₂ (IsLocalRing.closedPoint ℂ) := by
    intro he
    apply hxF
    apply Closed.Equalizer.mem_of_closed u v x hxc
    simpa only [p₁, p₂, p, Scheme.Hom.comp_apply, pointOfClosedPoint_apply] using he
  obtain ⟨i, hi⟩ := (PartialLinear.Projection.mem_domain X k L (u.left x)).mp hxU.1
  have hiv : PointFiberLinearForms.value X p₁ hp₁ (L i) ≠ 0 := by
    intro he
    have hm := (PointFiberLinearForms.value_zero X p₁ hp₁ (L i)).mp he
    have hep : p₁ (IsLocalRing.closedPoint ℂ) = u.left x :=
      congrArg u.left (pointOfClosedPoint_apply T.hom x hxc (IsLocalRing.closedPoint ℂ))
    exact hi (Eq.mp (congrArg (fun y : X.carrier =>
      (L i).val ∈ (X.embedding y).asHomogeneousIdeal) hep) hm)
  let N := LinearMap.ker (PairLinearConstraints.determinant X p₁ p₂ hp₁ hp₂ (L i))
  refine ⟨N, PairLinearConstraints.kernel_ne_top X p₁ p₂ hp₁ hp₂ hne (L i) (Or.inl hiv), ?_⟩
  intro a ha
  refine ⟨x, hxC, ?_⟩
  have hx : p (IsLocalRing.closedPoint ℂ) ∈ Projection.Coincidence.domain X k L u v := by
    simpa only [p, pointOfClosedPoint_apply] using hxU
  have he := CoincidenceExtension.excludes X k L u v a p hp hx i ha
  simpa only [p, pointOfClosedPoint_apply] using he

end

/-! A single new coordinate cuts all non-diagonal coincidence
components in finitely many schemes of pairs at once. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace FamilyCut

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

theorem exists_form (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    {τ ι κ : Type} [Finite τ] [Finite ι] [Finite κ]
    (T : τ → Over Foundations.Scheme.ProjectiveSpace.complexBase) [∀ t, NoetherianSpace (T t).left]
    [∀ t, LocallyOfFiniteType (T t).hom]
    (u v : ∀ t, T t ⟶ X.toOver)
    (z : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)
    (N : κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)) (hN : ∀ b, N b ≠ ⊤) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ b, a.val ∉ (z b).asHomogeneousIdeal) ∧ (∀ b, a ∉ N b) ∧
      ∀ t, ∀ C : irreducibleComponents (Projection.Coincidence.locus X k L (u t) (v t)),
        ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (T t).left (Projection.Coincidence.locus X k L (u t) (v t)) C : Set (T t).left) ⊆
          Closed.Equalizer.locus (u t) (v t) →
        ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport (T t).left (Projection.Coincidence.locus X k L (u t) (v t)) C,
          x ∉ Projection.Coincidence.locus X (k + 1) (Fin.cons a L) (u t) (v t) := by
  classical
  let S t := Projection.Coincidence.locus X k L (u t) (v t)
  let (t : τ) : NoetherianSpace (S t) := NoetherianSpace.set (S t : Set (T t).left)
  let (t : τ) : Finite (irreducibleComponents (S t)) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S t)).to_subtype
  let B := Σ t : τ, {C : irreducibleComponents (S t) //
    ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport (T t).left (S t) C : Set (T t).left) ⊆ Closed.Equalizer.locus (u t) (v t)}
  have hM (b : B) : ∃ M : Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1), M ≠ ⊤ ∧
      ∀ a ∉ M, ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport (T b.1).left (S b.1) b.2.val,
        x ∉ Projection.Coincidence.locus X (k + 1) (Fin.cons a L) (u b.1) (v b.1) :=
    exists_submodule X k L (u b.1) (v b.1) b.2.val b.2.property
  choose M hM hcut using hM
  let F : B ⊕ κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) := Sum.elim M N
  have hF : ∀ b, F b ≠ ⊤ := by
    intro b
    cases b with
    | inl b => exact hM b
    | inr b => exact hN b
  obtain ⟨a, ha, haF⟩ := ConstrainedLinearForms.exists_form X.ambientDimension z F hF
  refine ⟨a, ha, fun b => haF (Sum.inr b), ?_⟩
  intro t C hC
  exact hcut ⟨t, C, hC⟩ a (haF (Sum.inl ⟨t, C, hC⟩))

end FamilyCut

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IncidenceComponentConstraint
