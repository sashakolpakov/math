import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # Projective Smooth To -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth

noncomputable section

/-!
# Smoothness and integrality of the actual projective ambient scheme

The standard affine cover proves smoothness. The homogeneous zero ideal
is a generic point, which proves irreducibility and hence integrality.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smooth_projectiveSpaceToBase (n : ℕ) : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @AlgebraicGeometry.Smooth.{0})
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) (Foundations.Scheme.ProjectiveCoordinateCover.iSup_projectiveCoordinateOpen n)
  intro i
  rw [← Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec_over n i]
  have hs : Smooth (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth.{0})]
    change (algebraMap ℂ (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)).Smooth
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  exact smooth_comp _ _

/-- The homogeneous zero ideal is relevant because a projective coordinate
is a nonzero element of the irrelevant ideal. -/
def projectiveGenericPoint (n : ℕ) : ProjectiveSpectrum (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)).IsPrime; infer_instance
  not_irrelevant_le := by
    intro h
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
      (by decide : 0 < 1) (MvPolynomial.isHomogeneous_X ℂ (0 : Fin (n + 1))))
    change MvPolynomial.X (0 : Fin (n + 1)) ∈
      (⊥ : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)) at hx
    have hz := Ideal.mem_bot.mp hx
    exact MvPolynomial.X_ne_zero _ hz

theorem closure_projectiveGenericPoint (n : ℕ) :
    closure ({projectiveGenericPoint n} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) = Set.univ := by
  change closure ({projectiveGenericPoint n} :
    Set (ProjectiveSpectrum (Foundations.Scheme.ProjectiveSpace.projectiveGrading n))) = Set.univ
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  rw [ProjectiveSpectrum.vanishingIdeal_singleton]
  exact ProjectiveSpectrum.zeroLocus_bot (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

theorem irreducibleSpace_projectiveSpace (n : ℕ) : IrreducibleSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
  rw [← closure_projectiveGenericPoint n]
  exact isIrreducible_singleton.closure

theorem isIntegral_projectiveSpace (n : ℕ) : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  let : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := smooth_projectiveSpaceToBase n
  let : IsReduced (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let : IrreducibleSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := irreducibleSpace_projectiveSpace n
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth
