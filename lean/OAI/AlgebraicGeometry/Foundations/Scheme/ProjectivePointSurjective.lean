import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorPoint
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover
import OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint

/-! # Projective Point Surjective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointSurjective

noncomputable section

/-!
# Surjectivity ingredients for actual projective complex points

A scheme point over `Spec ℂ` in an affine polynomial chart is evaluation at
its coordinate values. The projective result uses these genuine affine
morphisms and the finite coordinate-open cover.
-/

set_option autoImplicit false
set_option warningAsError true

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Every morphism from `Spec ℂ` to a polynomial affine scheme over ℂ is
ordinary evaluation at a complex coordinate vector. -/
theorem affinePolynomialPoint_eq_eval {ι : Type}
    (p : ProjectiveSpace.complexBase ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      𝟙 ProjectiveSpace.complexBase) :
    ∃ a : ι → ℂ, p = Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  have hc : CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ) ≫ φ =
      𝟙 (CommRingCat.of ℂ) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id] using hp
  refine ⟨fun i => φ (MvPolynomial.X i), ?_⟩
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    have h := congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f c) hc
    simpa using h
  · intro i
    simp

/-- Every actual complex scheme point of projective space factors through
one of the actual coordinate open subschemes. -/
theorem projectivePoint_factors_coordinateOpen {n : ℕ}
    (p : ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n) :
    ∃ (i : Fin (n + 1)) (q : ProjectiveSpace.complexBase ⟶ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme),
      q ≫ (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι = p := by
  obtain ⟨i, hi⟩ := ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n (p (default : ProjectiveSpace.complexBase))
  have hr : Set.range p ⊆ Set.range (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change p x ∈ ProjectiveCoordinateCover.projectiveCoordinateOpen n i
    simpa only [Subsingleton.elim x (default : ProjectiveSpace.complexBase)] using hi
  exact ⟨i, IsOpenImmersion.lift (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι p hr,
    IsOpenImmersion.lift_fac (ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι p hr⟩

/-- Every actual projective complex point is given by polynomial evaluation
in one of the standard affine charts. -/
theorem projectivePoint_eq_affineChart {n : ℕ}
    (p : ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n)
    (hp : p ≫ ProjectiveSpace.projectiveSpaceToBase n = 𝟙 ProjectiveSpace.complexBase) :
    ∃ (i : Fin (n + 1)) (a : {j : Fin (n + 1) // j ≠ i} → ℂ),
      p = Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) ≫
        ProjectiveChart.projectiveAffineChartMap n i := by
  obtain ⟨i, q, hq⟩ := projectivePoint_factors_coordinateOpen p
  let g := q ≫ (ProjectiveChart.projectiveCoordinateIsoSpec n i).hom
  have hg : g ≫ ProjectiveChart.projectiveChartPolynomialToBase n i = 𝟙 ProjectiveSpace.complexBase := by
    dsimp [g]
    rw [Category.assoc, ProjectiveChart.projectiveCoordinateIsoSpec_over, ← Category.assoc, hq]
    exact hp
  obtain ⟨a, ha⟩ := affinePolynomialPoint_eq_eval g hg
  refine ⟨i, a, ?_⟩
  rw [← ha]
  simpa [g, ProjectiveChart.projectiveAffineChartMap, Category.assoc] using hq.symm

/-- Every actual complex point of the projective scheme is constructed from
a nonzero homogeneous coordinate vector. -/
theorem projectiveVectorPoint_surjective {n : ℕ}
    (p : ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n)
    (hp : p ≫ ProjectiveSpace.projectiveSpaceToBase n = 𝟙 ProjectiveSpace.complexBase) :
    ∃ (v : Fin (n + 1) → ℂ) (hv : v ≠ 0), ProjectiveVectorPoint.projectiveVectorPoint v hv = p := by
  obtain ⟨i, a, ha⟩ := projectivePoint_eq_affineChart p hp
  refine ⟨DehomogenizationC.Algebraic.Dehomogenization.insertOne i a, ProjectiveChartPoint.insertOne_ne_zero n i a, ?_⟩
  exact (ProjectiveChartPoint.projectiveAffineChartMap_eval_eq_vectorPoint n i a
    (ProjectiveChartPoint.insertOne_ne_zero n i a)).symm.trans ha.symm

/-- Equivalently, every actual complex projective scheme point comes from
mathlib's projectivization of the homogeneous coordinate vector space. -/
theorem exists_projectivizationPoint {n : ℕ}
    (p : ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n)
    (hp : p ≫ ProjectiveSpace.projectiveSpaceToBase n = 𝟙 ProjectiveSpace.complexBase) :
    ∃ q : Projectivization ℂ (Fin (n + 1) → ℂ), ProjectiveVectorScale.projectivizationPoint n q = p := by
  obtain ⟨v, hv, hpv⟩ := projectiveVectorPoint_surjective p hp
  exact ⟨Projectivization.mk ℂ v hv, (ProjectiveVectorScale.projectivizationPoint_mk v hv).trans hpv⟩

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointSurjective
