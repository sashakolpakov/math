import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Smooth Reduced Algebra -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReducedAlgebra.Construction

noncomputable section

/-! Reducedness of smooth algebras over fields for the Openness argument. -/

open scoped TensorProduct

/-- An etale algebra over a domain is reduced: flatness embeds it in its
generic fiber, which is unramified over a field and therefore reduced. -/
theorem isReduced_etale_algebra_of_domain
    (R B : Type*) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] : IsReduced B := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] B) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] B)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- A smooth algebra over a field is reduced. Locally, a smooth algebra
is etale over a polynomial algebra, to which the domain case applies. -/
theorem isReduced_smooth_algebra_of_field
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Algebra.Smooth K B] :
    IsReduced B := by
  constructor
  intro x hx
  apply eq_zero_of_localization x
  intro m hm
  have : m.IsMaximal := hm
  obtain ⟨f, hfm, n, _, _, hf⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := m)
  have : Algebra.IsStandardEtale (MvPolynomial (Fin n) K) (Localization.Away f) := hf
  have : IsReduced (Localization.Away f) :=
    isReduced_etale_algebra_of_domain (MvPolynomial (Fin n) K) (Localization.Away f)
  have hzero : algebraMap B (Localization.Away f) x = 0 :=
    (hx.map (algebraMap B (Localization.Away f))).eq_zero
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
    (Localization.Away f) x).mp hzero
  have hsub : Submonoid.powers f ≤ m.primeCompl := Submonoid.powers_le.mpr hfm
  exact (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) x).mpr
    ⟨⟨c, hsub c.property⟩, hc⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReducedAlgebra.Construction
