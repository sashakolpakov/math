import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Smooth Reduced Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothReducedOf.Construction.SmoothReduced

/-!
# Smooth algebras over fields are reduced

Locally a smooth algebra is étale over a polynomial algebra. Flatness embeds
each such chart into its generic fiber, which is unramified over a field and
hence reduced.
-/

open scoped TensorProduct

universe u v

/-- A flat unramified algebra over a domain embeds in its reduced generic
fiber, and is therefore reduced. -/
theorem of_flat_unramified_domain
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FormallyUnramified R A] [Algebra.FiniteType R A] : IsReduced A := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- Every smooth algebra over a field is reduced. -/
theorem of_smooth_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] :
    IsReduced A := by
  let D := {r : A | IsReduced (Localization.Away r)}
  have hD : Ideal.span D = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    let := hP
    obtain ⟨r, hr, n, a, ht, he⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := P)
    let := a
    let := ht
    let := he
    have hred : IsReduced (Localization.Away r) :=
      of_flat_unramified_domain (R := MvPolynomial (Fin n) K)
    exact hr (hle (Ideal.subset_span hred))
  have : ∀ r : D, IsReduced (Localization.Away r.val) := fun r => r.property
  exact isReduced_of_injective (algebraMap A (∀ r : D, Localization.Away r.val))
    (Localization.algebraMap_injective_of_span_eq_top D hD)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothReducedOf.Construction.SmoothReduced
