import OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint

/-! # Closure Chart Iff -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartIff.Constructions.ClosureChartPoints

noncomputable section

/-! # RiemannProjectivity: complex points of the native affine closure charts -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartF.Constructions.ClosureAffineChart OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {n : ℕ}

def evaluation (i : Fin (n + 1)) (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv _ (MvPolynomial.aeval a)

theorem evaluation_left (i : Fin (n + 1)) (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (evaluation i a).left = Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) := by
  rw [evaluation, AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem evaluation_projective (i : Fin (n + 1)) (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (evaluation i a).left ≫ AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i =
      (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (.mk ℂ (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i a))).left := by
  rw [evaluation_left, AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveAffineChartMap_eval_eq_vectorPoint]
  exact (AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale.projectivizationPoint_mk _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem exists_native_point_iff
    {S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))}
    (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)) (hQ : ∀ q ∈ Q, ∃ d, q.IsHomogeneous d)
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0})
    (i : Fin (n + 1)) (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (∃ q : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ ClosureChartF.Constructions.ClosureAffineChart.over S i, q ≫ ClosureChartF.Constructions.ClosureAffineChart.embedding S i = evaluation i a) ↔
      a ∈ ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S) i := by
  let p : Projectivization ℂ (Fin (n + 1) → ℂ) :=
    .mk ℂ (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i a)
  have hmem : a ∈ ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S) i ↔ p ∈ S :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff S (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i a)
  rw [hmem]
  constructor
  · rintro ⟨q, hq⟩
    have he : q.left ≫ ClosureChartF.Constructions.ClosureAffineChart.toAffine S i = (evaluation i a).left := congrArg Over.Hom.left hq
    have hp : q.left ≫ ClosureChartF.Constructions.ClosureAffineChart.toClosure S i ≫ ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S = (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left := by
      rw [show ClosureChartF.Constructions.ClosureAffineChart.toClosure S i ≫ ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S = ClosureChartF.Constructions.ClosureAffineChart.toAffine S i ≫ AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i
        from pullback.condition.symm, ← Category.assoc, he]
      exact evaluation_projective i a
    apply (ExactProjective.Constructions.ExactProjectiveClosure.underlying_mem_support_iff Q hQ hS p).mp
    have hpoint := congrArg (fun f : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n =>
      f (IsLocalRing.closedPoint ℂ)) hp
    change ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S ((ClosureChartF.Constructions.ClosureAffineChart.toClosure S i) (q.left (IsLocalRing.closedPoint ℂ))) =
      ProjectiveClosureIs.Constructions.ProjectiveClosure.underlyingPoint p at hpoint
    rw [← hpoint]
    exact (ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusion_range S).subset ⟨(ClosureChartF.Constructions.ClosureAffineChart.toClosure S i) (q.left (IsLocalRing.closedPoint ℂ)), rfl⟩
  · intro hp
    let r := ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedPoint S p (ProjectiveClosureIs.Constructions.ProjectiveClosure.underlying_mem_support S hp)
    have hr : r.left ≫ ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S = (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left :=
      congrArg Over.Hom.left (ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedPoint_inclusion S p (ProjectiveClosureIs.Constructions.ProjectiveClosure.underlying_mem_support S hp))
    have he : (evaluation i a).left ≫ AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i =
        r.left ≫ ProjectiveClosureIs.Constructions.ProjectiveClosure.closureInclusion S := (evaluation_projective i a).trans hr.symm
    let q₀ : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ ClosureChartF.Constructions.ClosureAffineChart.scheme S i := pullback.lift (evaluation i a).left r.left he
    have hq₀ : q₀ ≫ (ClosureChartF.Constructions.ClosureAffineChart.over S i).hom = 𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := by
      change q₀ ≫ ClosureChartF.Constructions.ClosureAffineChart.toAffine S i ≫ AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i = _
      rw [← Category.assoc]
      change (pullback.lift _ _ he ≫ pullback.fst _ _) ≫ _ = _
      rw [pullback.lift_fst]
      exact (evaluation i a).w
    refine ⟨Over.homMk q₀ hq₀, ?_⟩
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ he

theorem coordinate_range
    {S : Set (Projectivization ℂ (Fin (n + 1) → ℂ))}
    (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)) (hQ : ∀ q ∈ Q, ∃ d, q.IsHomogeneous d)
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0})
    (i : Fin (n + 1)) :
    range (AffineImageAlgebraEq.Constructions.AffineImageAlgebra.coordinates (AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra.coordinateHom (ClosureChartF.Constructions.ClosureAffineChart.over S i) (ClosureChartF.Constructions.ClosureAffineChart.embedding S i))) =
      ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone S) i := by
  let X := ClosureChartF.Constructions.ClosureAffineChart.over S i
  let j := ClosureChartF.Constructions.ClosureAffineChart.embedding S i
  let f := AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra.coordinateHom X j
  ext a
  rw [← exists_native_point_iff Q hQ hS i a]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨(AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X).symm q, ?_⟩
    rw [← AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra.coordinateHom_point]
    apply (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv _).congr_arg
    apply AlgHom.ext
    intro p
    exact (AffineImageAlgebraEq.Constructions.AffineImageAlgebra.eval_coordinates f q p).symm.trans
      (congrArg (fun a => MvPolynomial.eval a p) hq)
  · rintro ⟨q, hq⟩
    let r := AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X q
    refine ⟨r, ?_⟩
    have he : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv _ (r.comp f) = evaluation i a := by
      rw [AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra.coordinateHom_point]
      simpa only [r, Equiv.symm_apply_apply] using hq
    have hf : r.comp f = MvPolynomial.aeval a := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv _).injective he
    funext k
    change r (f (MvPolynomial.X k)) = a k
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using
      congrArg (fun f : AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i →ₐ[ℂ] ℂ => f (MvPolynomial.X k)) hf

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ClosureChartIff.Constructions.ClosureChartPoints
