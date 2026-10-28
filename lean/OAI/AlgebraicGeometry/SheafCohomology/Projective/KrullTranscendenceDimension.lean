import OAI.AlgebraicGeometry.SheafCohomology.Projective.NoetherNormalizationDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

/-! # Krull Transcendence Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.KrullTranscendenceDimension.Dimension

noncomputable section

/-! Krull dimension and the actual function-field transcendence dimension agree on affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ringKrullDim_eq_trdeg_toNat (K B : Type u) [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] :
    ringKrullDim B = ((Algebra.trdeg K B).toNat : WithBot ℕ∞) := by
  obtain ⟨g, φ, hφ, hfin, hdim⟩ := NoetherNormalizationDimension.Dimension.noetherNormalization_krullDimension K B
  have : IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr hfin
  have hint : φ.toRingHom.IsIntegral :=
    (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
  have htr := Foundations.Scheme.TranscendenceDegreeTransfer.trdeg_eq_of_injective_integral_algHom K φ hφ hint
  rw [MvPolynomial.trdeg_of_isDomain] at htr
  have hg : (Algebra.trdeg K B).toNat = g := by
    rw [← htr]
    simp
  rw [hg]
  exact hdim

theorem affine_chart_krullDimension {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ringKrullDim Γ(X, U) = (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f : WithBot ℕ∞) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU]
  exact ringKrullDim_eq_trdeg_toNat K Γ(X, U)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.KrullTranscendenceDimension.Dimension
