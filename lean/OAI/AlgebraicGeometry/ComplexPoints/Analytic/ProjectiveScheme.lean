import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCountability
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointInjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointSurjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveComplexPoints

/-! # Projective Scheme -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Ordinary complex points of the genuine projective scheme

The carrier on the scheme side is the actual type of morphisms over `Spec ℂ`.
Its topology is the affine-test topology from `SchemePoints`. The coordinate
chart maps below use the proved scheme isomorphisms of standard Proj opens.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

/-- An isomorphism of actual complex schemes induces a homeomorphism of their
complex-valued points with the affine-test topology. -/
def SchemePointHomeomorphs.schemeComplexPoints.homeomorphOfIso {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y) :
    SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ SchemePointHomeomorphs.schemeComplexPoints Y where
  toFun := SchemePointHomeomorphs.schemeComplexPoints.map e.hom
  invFun := SchemePointHomeomorphs.schemeComplexPoints.map e.inv
  left_inv x := by simp [SchemePointHomeomorphs.schemeComplexPoints.map, Category.assoc]
  right_inv x := by simp [SchemePointHomeomorphs.schemeComplexPoints.map, Category.assoc]
  continuous_toFun := SchemePointHomeomorphs.schemeComplexPoints.continuous_map e.hom
  continuous_invFun := SchemePointHomeomorphs.schemeComplexPoints.continuous_map e.inv

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.homeomorphOfIso_apply {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : X ≅ Y)
    (x : SchemePointHomeomorphs.schemeComplexPoints X) : SchemePointHomeomorphs.schemeComplexPoints.homeomorphOfIso e x = x ≫ e.hom := rfl

end

/-- The genuine complex-valued points of standard projective n-space. -/
abbrev ProjectiveScheme.projectiveSchemeComplexPoints (n : ℕ) :=
  SchemePointHomeomorphs.schemeComplexPoints (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))

/-- The nonzero-vector construction, descended to ordinary projective space,
viewed as an actual point over the complex base. -/
def ProjectiveScheme.projectivizationSchemePoint (n : ℕ)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) : ProjectiveScheme.projectiveSchemeComplexPoints n :=
  Over.homMk (Foundations.Scheme.ProjectiveVectorScale.projectivizationPoint n p) (Foundations.Scheme.ProjectiveVectorScale.projectivizationPoint_over_base p)

@[simp]
theorem ProjectiveScheme.projectivizationSchemePoint_left (n : ℕ)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    (ProjectiveScheme.projectivizationSchemePoint n p).left = Foundations.Scheme.ProjectiveVectorScale.projectivizationPoint n p := rfl

/-- The map into actual complex scheme points is injective. -/
theorem ProjectiveScheme.projectivizationSchemePoint_injective (n : ℕ) :
    Function.Injective (ProjectiveScheme.projectivizationSchemePoint n) := by
  intro p q h
  apply Foundations.Scheme.ProjectivePointInjective.projectivizationPoint_injective n
  exact congrArg (fun x : ProjectiveScheme.projectiveSchemeComplexPoints n => x.left) h

/-- Membership in the actual coordinate open agrees with the ordinary
nonvanishing-coordinate patch under the homogeneous-coordinate map. -/
theorem ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen (n : ℕ)
    (i : Fin (n + 1)) (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    (ProjectiveScheme.projectivizationSchemePoint n p).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
        Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i ↔
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p := by
  induction p using Projectivization.ind with
  | h v hv =>
      change Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint v hv (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
          Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i ↔
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (Projectivization.mk ℂ v hv)
      rw [Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff]
      exact Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint_mem_coordinateOpen_iff v hv i _

/-- The standard affine chart embedding as a morphism over `Spec ℂ`. -/
def ProjectiveScheme.projectiveAffineChartOverMap (n : ℕ) (i : Fin (n + 1)) :
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) ⟶
      Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
  Over.homMk (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i) (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over n i)

/-- The over-category chart map is still an actual open immersion. -/
instance ProjectiveScheme.projectiveAffineChartOverMap_isOpenImmersion (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (ProjectiveScheme.projectiveAffineChartOverMap n i).left := by
  change IsOpenImmersion (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i)
  infer_instance

/-- The points of a genuine Proj coordinate open have their usual affine
coordinate topology, by the actual scheme chart isomorphism. -/
def ProjectiveScheme.projectiveCoordinatePointHomeomorph (n : ℕ) (i : Fin (n + 1)) :
    SchemePointHomeomorphs.schemeComplexPoints
      (Over.mk ((Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) ≃ₜ
      ({j : Fin (n + 1) // j ≠ i} → ℂ) :=
  (SchemePointHomeomorphs.schemeComplexPoints.homeomorphOfIso (Foundations.Scheme.ProjectiveChart.projectiveCoordinateOverIso n i)).trans
    ((SchemePointHomeomorphs.affineSchemePointHomeomorph (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).symm.trans
      (PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}))

/-- Ordinary affine coordinates define actual projective scheme points through
the corresponding genuine affine chart embedding. -/
def ProjectiveScheme.projectiveAffineSchemePoint (n : ℕ) (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) : ProjectiveScheme.projectiveSchemeComplexPoints n :=
  SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (ProjectiveScheme.projectiveAffineChartOverMap n i)
    ((PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm z)

/-- This chart construction is continuous in ordinary complex coordinates. -/
theorem ProjectiveScheme.continuous_projectiveAffineSchemePoint (n : ℕ) (i : Fin (n + 1)) :
    Continuous (ProjectiveScheme.projectiveAffineSchemePoint n i) :=
  (SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap
    (CommAlgCat.of ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))
    (ProjectiveScheme.projectiveAffineChartOverMap n i)).comp
      (PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm.continuous

/-- The chart map on scheme morphisms is exactly polynomial evaluation followed
by the genuine affine chart insertion. -/
@[simp]
theorem ProjectiveScheme.projectiveAffineSchemePoint_left (n : ℕ) (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (ProjectiveScheme.projectiveAffineSchemePoint n i z).left =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval z)) ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i := by
  change (Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)
    ((PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm z)).left ≫
      Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i = _
  rw [Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left]
  rfl

/-- The affine scheme chart and the ordinary projective affine chart give
exactly the same complex-valued scheme point. -/
theorem ProjectiveScheme.projectiveAffineSchemePoint_eq_projectivization (n : ℕ)
    (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    ProjectiveScheme.projectiveAffineSchemePoint n i z =
      ProjectiveScheme.projectivizationSchemePoint n ((ProjectiveCharts.projectiveAffineChart i).symm z).val := by
  apply Over.OverMorphism.ext
  rw [ProjectiveScheme.projectiveAffineSchemePoint_left, ProjectiveScheme.projectivizationSchemePoint_left]
  change Spec.map (CommRingCat.ofHom (MvPolynomial.eval z)) ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i =
    Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i z) (Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i z)
  exact Foundations.Scheme.ProjectiveChartPoint.projectiveAffineChartMap_eval_eq_vectorPoint n i z (Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i z)

/-- On an ordinary coordinate patch, the global scheme-point map is given by
the genuine scheme chart followed by its ordinary affine coordinates. -/
theorem ProjectiveScheme.projectivizationSchemePoint_on_patch (n : ℕ) (i : Fin (n + 1))
    (p : {p : Projectivization ℂ (Fin (n + 1) → ℂ) //
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p}) :
    ProjectiveScheme.projectivizationSchemePoint n p.val =
      ProjectiveScheme.projectiveAffineSchemePoint n i (ProjectiveCharts.projectiveAffineChart i p) := by
  simpa only [Homeomorph.symm_apply_apply] using
    (ProjectiveScheme.projectiveAffineSchemePoint_eq_projectivization n i
      (ProjectiveCharts.projectiveAffineChart i p)).symm

/-- Ordinary homogeneous coordinates vary continuously as genuine scheme
points equipped with the affine-test topology. -/
theorem ProjectiveScheme.continuous_projectivizationSchemePoint (n : ℕ) :
    Continuous (ProjectiveScheme.projectivizationSchemePoint n) := by
  apply continuous_of_cover_nhds
    (s := fun i : Fin (n + 1) =>
      {p : Projectivization ℂ (Fin (n + 1) → ℂ) |
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p})
  · intro p
    obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch p
    exact ⟨i, (ProjectiveCharts.isOpen_projectivePatch i).mem_nhds hi⟩
  · intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun p : {p : Projectivization ℂ (Fin (n + 1) → ℂ) //
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} => ProjectiveScheme.projectivizationSchemePoint n p.val)
    have heq : (fun p : {p : Projectivization ℂ (Fin (n + 1) → ℂ) //
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p} => ProjectiveScheme.projectivizationSchemePoint n p.val) =
        (fun p => ProjectiveScheme.projectiveAffineSchemePoint n i (ProjectiveCharts.projectiveAffineChart i p)) :=
      funext (ProjectiveScheme.projectivizationSchemePoint_on_patch n i)
    rw [heq]
    exact (ProjectiveScheme.continuous_projectiveAffineSchemePoint n i).comp
      (ProjectiveCharts.projectiveAffineChart i).continuous

/-- Every genuine complex-valued point of the projective scheme has nonzero
homogeneous coordinates. -/
theorem ProjectiveScheme.projectivizationSchemePoint_surjective (n : ℕ) :
    Function.Surjective (ProjectiveScheme.projectivizationSchemePoint n) := by
  intro p
  obtain ⟨q, hq⟩ := Foundations.Scheme.ProjectivePointSurjective.exists_projectivizationPoint p.left (Over.w p)
  refine ⟨q, ?_⟩
  apply Over.OverMorphism.ext
  exact hq

/-- The genuine complex-valued points of projective n-space are compact for
their affine-test topology, as a continuous image of ordinary projective space. -/
instance ProjectiveScheme.projectiveSchemeComplexPoints_compactSpace (n : ℕ) :
    CompactSpace (ProjectiveScheme.projectiveSchemeComplexPoints n) :=
  Function.Surjective.compactSpace (ProjectiveScheme.continuous_projectivizationSchemePoint n)
    (ProjectiveScheme.projectivizationSchemePoint_surjective n)

/-- Standard affine coordinates map openly into the actual projective
scheme-point space, because the scheme chart is an open immersion. -/
theorem ProjectiveScheme.isOpenMap_projectiveAffineSchemePoint (n : ℕ) (i : Fin (n + 1)) :
    IsOpenMap (ProjectiveScheme.projectiveAffineSchemePoint n i) :=
  ((SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion
      (ProjectiveScheme.projectiveAffineChartOverMap n i)).comp
    (SchemePointHomeomorphs.affineSchemePointHomeomorph (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).isOpenMap).comp
      (PolynomialEvaluation.polynomialPointHomeomorph {j : Fin (n + 1) // j ≠ i}).symm.isOpenMap

/-- The homogeneous-coordinate map is open, as seen on the genuine standard
coordinate charts covering ordinary projective space. -/
theorem ProjectiveScheme.isOpenMap_projectivizationSchemePoint (n : ℕ) :
    IsOpenMap (ProjectiveScheme.projectivizationSchemePoint n) := by
  let s : Fin (n + 1) → Set (Projectivization ℂ (Fin (n + 1) → ℂ)) :=
    fun i => {p | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p}
  have hloc (i : Fin (n + 1)) :
      IsOpenMap (fun p : s i => ProjectiveScheme.projectivizationSchemePoint n p.val) := by
    have heq : (fun p : s i => ProjectiveScheme.projectivizationSchemePoint n p.val) =
        (fun p : s i => ProjectiveScheme.projectiveAffineSchemePoint n i
          (ProjectiveCharts.projectiveAffineChart i p)) :=
      funext (ProjectiveScheme.projectivizationSchemePoint_on_patch n i)
    rw [heq]
    exact (ProjectiveScheme.isOpenMap_projectiveAffineSchemePoint n i).comp
      (ProjectiveCharts.projectiveAffineChart i).isOpenMap
  intro U hU
  have himg : ProjectiveScheme.projectivizationSchemePoint n '' U =
      ⋃ i : Fin (n + 1), (fun p : s i => ProjectiveScheme.projectivizationSchemePoint n p.val) ''
        ((Subtype.val : s i → Projectivization ℂ (Fin (n + 1) → ℂ)) ⁻¹' U) := by
    ext q
    constructor
    · rintro ⟨p, hp, hpq⟩
      obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch p
      exact Set.mem_iUnion.mpr ⟨i, ⟨⟨p, hi⟩, hp, hpq⟩⟩
    · intro hq
      obtain ⟨i, p, hp, hpq⟩ := Set.mem_iUnion.mp hq
      exact ⟨p.val, hp, hpq⟩
  rw [himg]
  exact isOpen_iUnion fun i => hloc i _ (hU.preimage continuous_subtype_val)

/-- Ordinary complex projective space is homeomorphic to the actual complex
points of the standard projective scheme with their independently defined
affine-test topology. -/
def ProjectiveScheme.projectiveSchemePointHomeomorph (n : ℕ) :
    Projectivization ℂ (Fin (n + 1) → ℂ) ≃ₜ ProjectiveScheme.projectiveSchemeComplexPoints n :=
  (Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n).toHomeomorphOfContinuousOpen
    (ProjectiveScheme.continuous_projectivizationSchemePoint n) (ProjectiveScheme.isOpenMap_projectivizationSchemePoint n)

/-- The topological comparison has the genuine homogeneous-coordinate map as
its forward function. -/
@[simp]
theorem ProjectiveScheme.projectiveSchemePointHomeomorph_apply (n : ℕ)
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) :
    ProjectiveScheme.projectiveSchemePointHomeomorph n p = ProjectiveScheme.projectivizationSchemePoint n p := rfl

/-- Actual projective scheme complex points are Hausdorff for the existing
ordinary affine-test topology. -/
instance ProjectiveScheme.projectiveSchemeComplexPoints_t2Space (n : ℕ) :
    T2Space (ProjectiveScheme.projectiveSchemeComplexPoints n) :=
  (ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.isEmbedding.t2Space

/-- Actual projective scheme complex points have a countable topological basis. -/
instance ProjectiveScheme.projectiveSchemeComplexPoints_secondCountableTopology (n : ℕ) :
    SecondCountableTopology (ProjectiveScheme.projectiveSchemeComplexPoints n) :=
  (ProjectiveScheme.projectiveSchemePointHomeomorph n).symm.secondCountableTopology

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
