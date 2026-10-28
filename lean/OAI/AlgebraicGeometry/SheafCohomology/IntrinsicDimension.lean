import OAI.AlgebraicGeometry.SheafCohomology.Projective.KrullTranscendenceDimension
import OAI.AlgebraicGeometry.SheafCohomology.DimensionBound

/-! # Intrinsic Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.IntrinsicDimension.Projective

noncomputable section

/-! The scheme's topological Krull dimension equals its actual function-field dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem topologicalKrullDim_openImmersion_le {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [Projective.IntegralDimension.Dimension.topologicalKrullDim_eq_specialization_krullDim,
    Projective.IntegralDimension.Dimension.topologicalKrullDim_eq_specialization_krullDim,
    Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  rw [← coheight_eq_of_isOpenImmersion f (x := x)]
  exact Order.coheight_le_krullDim (f x)

theorem topologicalKrullDim_eq_schemeTranscendenceDimension
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    topologicalKrullDim X = (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f : WithBot ℕ∞) := by
  apply le_antisymm (DimensionBound.Projective.topologicalKrullDim_le_schemeTranscendenceDimension f)
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := (⊤ : X.Opens)) (by trivial)
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [← Projective.KrullTranscendenceDimension.Dimension.affine_chart_krullDimension f U hU,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_openImmersion_le hU.fromSpec

end

end OAI.AlgebraicGeometry.SheafCohomology.IntrinsicDimension.Projective
