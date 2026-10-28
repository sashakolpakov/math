import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Real Fourier -/

namespace OAI.RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction

noncomputable section

section

/-! Descent of Schwartz lattice sums to the real unit torus. -/

open scoped Classical

variable {ι : Type*} [Fintype ι]

def integerReal (n : ι → ℤ) : ι → ℝ := fun i => (n i : ℝ)

theorem integerReal_mem_lattice (n : ι → ℤ) : integerReal n ∈ AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι := by
  apply ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨n i, by simp [integerReal]⟩

def integerLatticeEquiv : (ι → ℤ) ≃ AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι :=
  Equiv.ofBijective (fun n => ⟨integerReal n, integerReal_mem_lattice n⟩) (by
    constructor
    · intro m n h
      funext i
      have hi : (m i : ℝ) = (n i : ℝ) := congrFun (congrArg Subtype.val h) i
      exact_mod_cast hi
    · intro a
      have ha := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ a.val).mp a.property
      have h : ∀ i, ∃ m : ℤ, (m : ℝ) = a.val i := by
        intro i
        simpa using ha i
      choose m hm using h
      exact ⟨m, Subtype.ext (funext hm)⟩)

theorem integerLatticeEquiv_apply (n : ι → ℤ) :
    (integerLatticeEquiv n).val = integerReal n := rfl

def torusProjection (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

omit [Fintype ι] in
theorem torusProjection_isOpenQuotientMap : IsOpenQuotientMap
    (torusProjection : (ι → ℝ) → UnitAddTorus ι) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

theorem torusProjection_eq_iff (x y : ι → ℝ) :
    torusProjection x = torusProjection y ↔ x - y ∈ AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι := by
  change torusProjection x = torusProjection y ↔
    x - y ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ]
  constructor
  · intro h i
    have hi : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun h i
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp hi)
    exact ⟨n, by simpa using hn⟩
  · intro h
    funext i
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    obtain ⟨n, hn⟩ := h i
    apply AddSubgroup.mem_zmultiples_iff.mpr
    exact ⟨n, by simpa using hn⟩

theorem latticePeriodization_eq_of_projection_eq (f : SchwartzMap (ι → ℝ) ℂ)
    {x y : ι → ℝ} (h : torusProjection x = torusProjection y) :
    PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f x =
      PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f y := by
  let a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι := ⟨x - y, (torusProjection_eq_iff x y).mp h⟩
  have hxy : x = y + a.val := by dsimp [a]; abel
  rw [hxy]
  exact PoissonAutomorphyNormalizationData.Construction.latticePeriodization_add _ f a y

def torusRepresentative (t : UnitAddTorus ι) : ι → ℝ :=
  (torusProjection_isOpenQuotientMap.surjective t).choose

omit [Fintype ι] in
theorem torusRepresentative_projection (t : UnitAddTorus ι) :
    torusProjection (torusRepresentative t) = t :=
  (torusProjection_isOpenQuotientMap.surjective t).choose_spec

def torusPeriodization (f : SchwartzMap (ι → ℝ) ℂ) : C(UnitAddTorus ι, ℂ) where
  toFun t := PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f (torusRepresentative t)
  continuous_toFun := by
    apply torusProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
    have heq : (fun x : ι → ℝ =>
        PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f
          (torusRepresentative (torusProjection x))) =
        PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f := by
      funext x
      exact latticePeriodization_eq_of_projection_eq f (torusRepresentative_projection _)
    change Continuous (fun x : ι → ℝ => _)
    simp only [Function.comp_def]
    rw [heq]
    exact (PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f).continuous

theorem torusPeriodization_projection (f : SchwartzMap (ι → ℝ) ℂ) (x : ι → ℝ) :
    torusPeriodization f (torusProjection x) = ∑' n : ι → ℤ, f (x + integerReal n) := by
  change PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f
    (torusRepresentative (torusProjection x)) = _
  rw [latticePeriodization_eq_of_projection_eq f (torusRepresentative_projection _),
    PoissonAutomorphyNormalizationData.Construction.latticePeriodization_apply]
  exact (integerLatticeEquiv.tsum_eq (fun a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι => f (x + a.val))).symm

theorem integer_schwartz_summable (f : SchwartzMap (ι → ℝ) ℂ) :
    Summable (fun n : ι → ℤ => ‖f (integerReal n)‖) := by
  have h : Summable (fun n : ι → ℤ => ‖f (integerLatticeEquiv (ι := ι) n).val‖) :=
    (PoissonAutomorphyNormalizationData.Construction.schwartz_lattice_summable (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f).comp_injective
      (integerLatticeEquiv (ι := ι)).injective
  exact h

end

/-! The coordinate Fourier transform preserves the real Schwartz space. -/

open scoped Classical FourierTransform
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι]

def coordinateFourier (f : SchwartzMap (ι → ℝ) ℂ) : SchwartzMap (ι → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)) f))

theorem coordinateFourier_apply (f : SchwartzMap (ι → ℝ) ℂ) (x : ι → ℝ) :
    coordinateFourier f x = PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f x := by
  change 𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)) f : SchwartzMap (EuclideanSpace ℝ ι) ℂ))
      (WithLp.toLp 2 x) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [Circle.smul_def, smul_eq_mul, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, PoissonAutomorphyNormalizationData.standardRealCharacter,
      MonoidHom.compAddChar_apply]
    change (Real.fourierChar (-(∑ i, x i * y i)) : ℂ) * f y =
      f y * (Real.fourierChar (-(∑ i, x i * y i)) : ℂ)
    exact mul_comm _ _

theorem coordinateFourier_integer_summable (f : SchwartzMap (ι → ℝ) ℂ) :
    Summable (fun n : ι → ℤ => ‖PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (integerReal n)‖) := by
  simpa only [coordinateFourier_apply] using integer_schwartz_summable (coordinateFourier f)

end

end OAI.RepresentationTheory.Theta.RealFourier.PoissonAutomorphyConstruction
