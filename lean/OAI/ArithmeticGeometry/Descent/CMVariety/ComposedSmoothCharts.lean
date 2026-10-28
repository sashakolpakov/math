import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts

/-! # Composed Smooth Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ComposedSmoothCharts.Abelian.RelativeCharts

noncomputable section

section

/-!
Actual local submersion coordinates for a tower with standard-smooth
algebra presentations. The chart for the composite presentation retains
the free base coordinates, so the actual map on algebra points is a
surjective linear coordinate projection in these charts.

This constructs the local comparison from the polynomial presentations;
no local analytic trivialization or period comparison is assumed.
-/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
open scoped Classical ContDiff

variable {R A I J Sigma Tau : Type}
  [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]
  [Algebra R A] [IsScalarTower ℂ R A]
  [Fintype I] [Fintype J] [Fintype Sigma] [Fintype Tau]

def baseFreeIndex (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) :
    AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map := fun i =>
  ⟨Sum.inr i.val, by
    rintro ⟨j, hj⟩
    rcases j with j | j
    · cases hj
    · exact i.property ⟨j, Sum.inr.inj hj⟩⟩

omit [Fintype I] [Fintype J] in
theorem baseFreeIndex_injective (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) :
    Function.Injective (baseFreeIndex P Q) := by
  intro i j h
  apply Subtype.ext
  exact Sum.inr.inj (congrArg Subtype.val h)

/-- Projection to the base's free coordinates in the composite smooth chart. -/
def baseProjection (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) :
    (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map → ℂ) →L[ℂ] (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (baseFreeIndex P Q i))

omit [Fintype I] [Fintype J] in
theorem baseProjection_surjective (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) : Function.Surjective (baseProjection P Q) := by
  intro v
  refine ⟨Function.extend (baseFreeIndex P Q) v 0, funext (fun i => ?_)⟩
  exact (baseFreeIndex_injective P Q).extend_apply v 0 i

/-- Simultaneous actual charts in which the base map is a coordinate
projection. Their inverse charts evaluate every regular function
analytically, and the total chart maps into the base chart. -/
theorem exists_compatible_smooth_charts_with_coordinates
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ (eR : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (eA : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map → ℂ)),
      x.comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source ∧ x ∈ eA.source ∧
      (∀ z ∈ eA.target,
        (eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source) ∧
      (∀ z ∈ eA.target,
        eR ((eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A)) = baseProjection P Q z) ∧
      (∀ a : A, ContDiffOn ℂ ω (fun z => eA.symm z a) eA.target) ∧
      (∀ r : R, ContDiffOn ℂ ω (fun z => eR.symm z r) eR.target) ∧
      (∀ y i, eR y i = y (P.val i.val)) ∧
      (∀ y i, eA y i = y ((Q.comp P).val i.val)) := by
  let f := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ R A)
  obtain ⟨eR, hxR, hR, hiR⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts.exists_standardSmooth_point_chart P (f x)
  obtain ⟨e₀, hx₀, h₀, hi₀⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts.exists_standardSmooth_point_chart (Q.comp P) x
  let U := f ⁻¹' eR.source
  have hU : IsOpen U := eR.open_source.preimage f.continuous
  let eA := e₀.restrOpen U hU
  have hproj (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) : eR (f y) = baseProjection P Q (e₀ y) := by
    ext i
    rw [hR]
    change y (algebraMap R A (P.val i.val)) = e₀ y (baseFreeIndex P Q i)
    rw [h₀]
    rfl
  refine ⟨eR, eA, hxR, ⟨hx₀, hxR⟩, ?_, ?_, ?_, hiR, hR, h₀⟩
  · intro z hz
    exact hz.2
  · intro z hz
    change eR (f (e₀.symm z)) = baseProjection P Q z
    rw [hproj, e₀.right_inv hz.1]
  · intro a
    exact (hi₀ a).mono (fun _ hz => hz.1)

/-- The compatible-chart conclusion without the additional forward formulas. -/
theorem exists_compatible_smooth_charts
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ (eR : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (eA : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map → ℂ)),
      x.comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source ∧ x ∈ eA.source ∧
      (∀ z ∈ eA.target,
        (eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source) ∧
      (∀ z ∈ eA.target,
        eR ((eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A)) = baseProjection P Q z) ∧
      (∀ a : A, ContDiffOn ℂ ω (fun z => eA.symm z a) eA.target) ∧
      (∀ r : R, ContDiffOn ℂ ω (fun z => eR.symm z r) eR.target) := by
  obtain ⟨eR, eA, hxR, hxA, hs, hp, hiA, hiR, _, _⟩ :=
    exists_compatible_smooth_charts_with_coordinates P Q x
  exact ⟨eR, eA, hxR, hxA, hs, hp, hiA, hiR⟩

end

/-!
Split the actual free coordinates of a composite standard-smooth
presentation into base and fiber coordinates. The resulting chart
intertwines the actual map of algebra points with the first projection.
-/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts
open scoped Classical ContDiff

variable {R A I J Sigma Tau : Type}
  [CommRing R] [Algebra ℂ R] [CommRing A] [Algebra ℂ A]
  [Algebra R A] [IsScalarTower ℂ R A]
  [Fintype I] [Fintype J] [Fintype Sigma] [Fintype Tau]

def freeCoordinateSplit (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) :
    AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map ≃ AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map ⊕ AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.map where
  toFun w := match w with
    | ⟨Sum.inl j, hj⟩ => Sum.inr ⟨j, by
        rintro ⟨t, ht⟩
        exact hj ⟨Sum.inl t, congrArg Sum.inl ht⟩⟩
    | ⟨Sum.inr i, hi⟩ => Sum.inl ⟨i, by
        rintro ⟨t, ht⟩
        exact hi ⟨Sum.inr t, congrArg Sum.inr ht⟩⟩
  invFun w := match w with
    | Sum.inl i => baseFreeIndex P Q i
    | Sum.inr j => ⟨Sum.inl j.val, by
        rintro ⟨t, ht⟩
        rcases t with t | t
        · exact j.property ⟨t, Sum.inl.inj ht⟩
        · cases ht⟩
  left_inv w := by
    rcases w with ⟨w, hw⟩
    cases w <;> rfl
  right_inv w := by
    rcases w with ⟨i, hi⟩ | ⟨j, hj⟩ <;> rfl

def productCoordinates (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) :
    (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map → ℂ) ≃L[ℂ]
      ((AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) × (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.map → ℂ)) :=
  ((LinearEquiv.funCongrLeft ℂ ℂ (freeCoordinateSplit P Q).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.map) ℂ ℂ)).toContinuousLinearEquiv

theorem productCoordinates_fst (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) (z : AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates (Q.comp P).map → ℂ) :
    (productCoordinates P Q z).1 = baseProjection P Q z := rfl

/-- The standard-smooth algebra family is locally a first coordinate
projection on an open subset of a product of complex vector spaces. -/
theorem exists_smooth_product_charts
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (Q : Algebra.SubmersivePresentation R A J Tau) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ (eR : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (eA : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
        ((AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) × (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates Q.map → ℂ))),
      x.comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source ∧ x ∈ eA.source ∧
      (∀ z ∈ eA.target,
        (eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A) ∈ eR.source) ∧
      (∀ z ∈ eA.target,
        eR ((eA.symm z).comp (IsScalarTower.toAlgHom ℂ R A)) = z.1) := by
  obtain ⟨eR, e₀, hxR, hx₀, hsource, hproj, _, _⟩ := exists_compatible_smooth_charts P Q x
  let e := productCoordinates P Q
  refine ⟨eR, e₀.transHomeomorph e.toHomeomorph, hxR, hx₀, ?_, ?_⟩
  · intro z hz
    exact hsource (e.symm z) hz
  · intro z hz
    change eR ((e₀.symm (e.symm z)).comp (IsScalarTower.toAlgHom ℂ R A)) = z.1
    rw [hproj (e.symm z) hz, ← productCoordinates_fst]
    exact congrArg Prod.fst (e.apply_symm_apply z)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ComposedSmoothCharts.Abelian.RelativeCharts
