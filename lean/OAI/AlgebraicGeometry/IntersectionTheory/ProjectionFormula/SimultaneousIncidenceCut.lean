import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedDifferenceDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceBaseLocus

/-! # Simultaneous Incidence Cut -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousIncidenceCut

noncomputable section

/-! One linear form cuts every old coincidence component away from
the original diagonal while satisfying further finite linear avoidance constraints. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

instance over_separated (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : IsSeparated X.toOver.hom :=
  inferInstanceAs (IsSeparated X.structureMap)

instance over_finiteType (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : LocallyOfFiniteType X.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType X.structureMap)

theorem exists_form (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [NoetherianSpace T.left] [LocallyOfFiniteType T.hom]
    (u v : T ⟶ X.toOver)
    {ι κ : Type} [Finite ι] [Finite κ]
    (z : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)
    (N : κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)) (hN : ∀ b, N b ≠ ⊤) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ b, a.val ∉ (z b).asHomogeneousIdeal) ∧ (∀ b, a ∉ N b) ∧
      ∀ C : irreducibleComponents (Projection.Coincidence.locus X k L u v),
        ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport T.left (Projection.Coincidence.locus X k L u v) C : Set T.left) ⊆
          Closed.Equalizer.locus u v →
        ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport T.left (Projection.Coincidence.locus X k L u v) C,
          x ∉ Projection.Coincidence.locus X (k + 1) (Fin.cons a L) u v := by
  classical
  let S := Projection.Coincidence.locus X k L u v
  let F := Closed.Equalizer.locus u v
  let U := Projection.Coincidence.domain X k L u v
  let A := CoincidenceClosedPointTest.OpenClosure.openLocus U (Projection.Coincidence.first X k L u v) (Projection.Coincidence.second X k L u v)
  let : NoetherianSpace S := NoetherianSpace.set (S : Set T.left)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  let B := {C : irreducibleComponents S //
    ¬ (CycleClass.Thom.IntersectionGeometry.closedComponentSupport T.left S C : Set T.left) ⊆ F}
  have hw (b : B) : ∃ x : T.left, x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport T.left S b.val ∧
      x ∈ U ∧ x ∉ F ∧ IsClosed ({x} : Set T.left) :=
    ClosedDifferenceDimension.ClosureComponentWitness.closed_witness T.hom U A F b.val b.property
  choose x hxC hxU hxF hxc using hw
  let p b := pointOfClosedPoint T.hom (x b) (hxc b)
  have hp b : p b ≫ T.hom = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let p₁ b := p b ≫ u.left
  let p₂ b := p b ≫ v.left
  have hp₁ b : p₁ b ≫ X.structureMap = 𝟙 _ := CoincidenceExtension.point_over X u (p b) (hp b)
  have hp₂ b : p₂ b ≫ X.structureMap = 𝟙 _ := CoincidenceExtension.point_over X v (p b) (hp b)
  have hne b : p₁ b (IsLocalRing.closedPoint ℂ) ≠ p₂ b (IsLocalRing.closedPoint ℂ) := by
    intro he
    apply hxF b
    apply Closed.Equalizer.mem_of_closed u v (x b) (hxc b)
    simpa only [p₁, p₂, p, Scheme.Hom.comp_apply, pointOfClosedPoint_apply] using he
  have hi b : ∃ i, PointFiberLinearForms.value X (p₁ b) (hp₁ b) (L i) ≠ 0 := by
    obtain ⟨i, hi⟩ := (PartialLinear.Projection.mem_domain X k L (u.left (x b))).mp (hxU b).1
    refine ⟨i, ?_⟩
    intro he
    have hm := (PointFiberLinearForms.value_zero X (p₁ b) (hp₁ b) (L i)).mp he
    have hep : p₁ b (IsLocalRing.closedPoint ℂ) = u.left (x b) :=
      congrArg u.left (pointOfClosedPoint_apply T.hom (x b) (hxc b) (IsLocalRing.closedPoint ℂ))
    exact hi (Eq.mp (congrArg (fun y : X.carrier =>
      (L i).val ∈ (X.embedding y).asHomogeneousIdeal) hep) hm)
  choose j hj using hi
  let M : B ⊕ κ → Submodule ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) := Sum.elim
    (fun b => LinearMap.ker (PairLinearConstraints.determinant X (p₁ b) (p₂ b) (hp₁ b) (hp₂ b) (L (j b)))) N
  have hM : ∀ b, M b ≠ ⊤ := by
    intro b
    cases b with
    | inl b =>
      exact PairLinearConstraints.kernel_ne_top X (p₁ b) (p₂ b) (hp₁ b) (hp₂ b)
        (hne b) (L (j b)) (Or.inl (hj b))
    | inr b => exact hN b
  obtain ⟨a, ha, haM⟩ := ConstrainedLinearForms.exists_form X.ambientDimension z M hM
  refine ⟨a, ha, fun b => haM (Sum.inr b), ?_⟩
  intro C hC
  let b : B := ⟨C, hC⟩
  refine ⟨x b, hxC b, ?_⟩
  have hx : p b (IsLocalRing.closedPoint ℂ) ∈ Projection.Coincidence.domain X k L u v := by
    simpa only [p, pointOfClosedPoint_apply] using hxU b
  have he := CoincidenceExtension.excludes X k L u v a (p b) (hp b) hx (j b) (haM (Sum.inl b))
  simpa only [p, pointOfClosedPoint_apply] using he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousIncidenceCut
