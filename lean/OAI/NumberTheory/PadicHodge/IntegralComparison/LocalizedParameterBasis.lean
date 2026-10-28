import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBasisTransport

/-! # Localized Parameter Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedParameterBasis.ConormalBases

noncomputable section

/-! The transported quotient differential basis consists of the literal
differentials of the restricted parameter lifts. -/

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A)
  {g : ℕ} (b : Module.Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k])
  (t : Fin g → A)
  (hb : ∀ i, b i = KaehlerDifferential.D k (A ⧸ I) (Ideal.Quotient.mk I (t i)))

include hb in
theorem quotientBasis_equations (i : Fin g) :
    LocalizedConormalBases.quotientBasis (B := B) r I b i =
    KaehlerDifferential.D k (B ⧸ LocalizedConormalBases.extendedIdeal (B := B) I)
      (Ideal.Quotient.mk (LocalizedConormalBases.extendedIdeal (B := B) I) (algebraMap A B (t i))) := by
  rw [LocalizedConormalBases.quotientBasis_apply, hb, KaehlerDifferential.map_D]
  rfl

include hb in
theorem quotientBasisOfEq_equations (J : Ideal B) (hJ : I.map (algebraMap A B) = J)
    (i : Fin g) :
    LocalizedConormalBasisTransport.Bases.quotientBasisOfEq r I J hJ b i =
    KaehlerDifferential.D k (B ⧸ J)
      (Ideal.Quotient.mk J (algebraMap A B (t i))) := by
  subst J
  exact quotientBasis_equations r I b t hb i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedParameterBasis.ConormalBases
