import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Dimension
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Projective Dimension Bound -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDimensionBound

noncomputable section

/-! The relative dimension of projective space is the number of affine
coordinates. Closed projective embeddings consequently bound the dimension
of every nonempty smooth component. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem polynomial_relativeDimension (ι : Type) [Fintype ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card ι) ℂ (MvPolynomial ι ℂ) := by
  let : Algebra.IsStandardSmooth ℂ (MvPolynomial ι ℂ) :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential
      (KaehlerDifferential.mvPolynomialBasis ℂ ι) (by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply ℂ ι i).symm⟩)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  simpa using (KaehlerDifferential.mvPolynomialBasis ℂ ι).mk_eq_rank.symm

theorem chart_relativeDimension (n : ℕ) (i : Fin (n + 1)) :
    SmoothOfRelativeDimension n (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i) := by
    simpa only [Foundations.Scheme.ProjectiveChart.projectiveChartCoordinate_card] using
      polynomial_relativeDimension {j : Fin (n + 1) // j ≠ i}
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension n
    (MvPolynomial.C : ℂ →+* Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)
  rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  infer_instance

def projectiveCover (n : ℕ) : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1))
    (fun i => Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)))
    (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n) (by
      intro x
      obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n x
      refine ⟨i, (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ⟨x, hi⟩, ?_⟩
      change ((Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).hom ≫ (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv ≫
        (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι) ⟨x, hi⟩ = x
      simp) (fun _ => inferInstance)

theorem projective_relativeDimension (n : ℕ) :
    SmoothOfRelativeDimension n (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
  have : ∀ i, IsAffine ((projectiveCover n).X i) :=
    fun i => inferInstanceAs (IsAffine (Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))))
  apply HasRingHomProperty.of_source_openCover
    (P := @SmoothOfRelativeDimension n) (projectiveCover n)
  intro i
  have h : SmoothOfRelativeDimension n
      (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
    rw [Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over]
    exact chart_relativeDimension n i
  exact HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension n) _ h

def projectiveGenericPoint (n : ℕ) : Foundations.Scheme.ProjectiveSpace.projectiveSpace n where
  asHomogeneousIdeal := ⊥
  isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; infer_instance
  not_irrelevant_le := by
    intro h
    have hX : MvPolynomial.X (0 : Fin (n + 1)) ∈
        HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X ℂ (0 : Fin (n + 1)))
    exact MvPolynomial.X_ne_zero _ (Ideal.mem_bot.mp (h hX))

theorem projective_integral (n : ℕ) : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  have hd : closure ({projectiveGenericPoint n} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply (ProjectiveSpectrum.le_iff_mem_closure
      (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (projectiveGenericPoint n) x).mp
    change (⊥ : HomogeneousIdeal (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)) ≤ x.asHomogeneousIdeal
    exact bot_le
  let : IrreducibleSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
    rw [← hd]
    exact isIrreducible_singleton.closure)
  let : SmoothOfRelativeDimension n (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := projective_relativeDimension n
  let : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := SmoothOfRelativeDimension.smooth n _
  let : IsReduced (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem integral_dimension_le (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap ≤ V.ambientDimension := by
  let : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace V.ambientDimension) := projective_integral _
  let : SmoothOfRelativeDimension V.ambientDimension
      (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.ambientDimension) := projective_relativeDimension _
  let : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.ambientDimension) :=
    SmoothOfRelativeDimension.smooth V.ambientDimension _
  have h := Foundations.Scheme.ClosedImmersionDimension.closedImmersion_functionField_trdeg_le V.presentation.embedding
    (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.ambientDimension)
  rw [V.presentation.embedding_over] at h
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra V.structureMap
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.ambientDimension)
  change Algebra.trdeg ℂ V.carrier.functionField ≤
    Algebra.trdeg ℂ (Foundations.Scheme.ProjectiveSpace.projectiveSpace V.ambientDimension).functionField at h
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast V.structureMap,
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.ambientDimension),
    Intersection.Dimension.integral_dimension_of_relativeDimension
      (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.ambientDimension) V.ambientDimension] at h
  exact_mod_cast h

theorem relativeDimension_le (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (x : X.carrier) :
    m ≤ X.ambientDimension := by
  let C : irreducibleComponents X.carrier :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have h := integral_dimension_le (X.componentVariety C)
  rw [Intersection.Dimension.component_dimension X m C] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveDimensionBound
