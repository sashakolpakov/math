import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrimeModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AuxiliaryPrimeLevel

/-! # Models From Pure Factory -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsFromPureFactory

noncomputable section

/-! Actual pure models at sufficiently large levels give the arithmetic
prime models used by IntegralModel. Only one finite integer denominator is enlarged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem arithmeticPrimePELModels_of_pure_models
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (B d : ℕ) (hd : 0 < d)
    (hPure : ∀ (p : ℕ) [NeZero p], 3 ≤ p → B < p →
      ∀ (R : Type) [CommRing R] [IsNoetherianRing R],
        IsUnit (p : R) → IsUnit (2 : R) → IsUnit (d : R) →
        IsUnit ((∏ i, P.polarizationType i) : R) →
        ∃ M : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType p (Spec (.of R)),
          Nonempty (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) ∧ M.IsFine)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) : Arithmetic.PrimeModels.ArithmeticPrimePELModels P := by
  constructor
  intro K _ _ κ N _ _hs hδ _hchain iota
  let δ₀ := ∏ i, P.polarizationType i
  have hδ₀ : 0 < δ₀ := Finset.prod_pos (fun i _ => hδ i)
  obtain ⟨p, hp, hp3, hpδ, hpN, hpB⟩ :=
    AuxiliaryPrimeLevel.exists_auxiliary_prime_level_above δ₀ N B hδ₀ (NeZero.pos N)
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨G⟩ := CM.GeneratorReconstruction.cm_integral_generator_data_exists E
  let D₀ := N * p * δ₀ * G.conductor
  have hD₀ : D₀ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (NeZero.ne N) hp.ne_zero)
    (ne_of_gt hδ₀)) G.conductor_ne_zero
  let D := D₀ * (2 * d)
  have hD : D ≠ 0 := mul_ne_zero hD₀ (mul_ne_zero (by decide) (ne_of_gt hd))
  let L : Arithmetic.Open.FiniteNumberFieldExtension K := { carrier := K }
  let A : Base.ArithmeticBaseExtension K κ := {
    extension := L
    embedding := κ
    embedding_extends := by ext x; rfl
    denominator := D
    denominator_ne_zero := hD }
  have hbase : D₀ ∣ D := dvd_mul_right D₀ (2 * d)
  have hNdiv : N ∣ D := ((dvd_mul_right N p).trans
    ((dvd_mul_right (N * p) δ₀).trans (dvd_mul_right (N * p * δ₀) G.conductor))).trans hbase
  have hpdiv : p ∣ D := ((dvd_mul_left p N).trans
    ((dvd_mul_right (N * p) δ₀).trans (dvd_mul_right (N * p * δ₀) G.conductor))).trans hbase
  have hδdiv : δ₀ ∣ D := ((dvd_mul_left δ₀ (N * p)).trans
    (dvd_mul_right (N * p * δ₀) G.conductor)).trans hbase
  have hcdiv : G.conductor ∣ D := (dvd_mul_left G.conductor (N * p * δ₀)).trans hbase
  have h2div : 2 ∣ D := (dvd_mul_right 2 d).trans (dvd_mul_left (2 * d) D₀)
  have hddiv : d ∣ D := (dvd_mul_left d 2).trans (dvd_mul_left (2 * d) D₀)
  obtain ⟨M, ⟨Q⟩, hM⟩ := hPure p hp3 hpB A.R
    (A.divisor_isUnit p hpdiv) (A.divisor_isUnit 2 h2div) (A.divisor_isUnit d hddiv)
    (by simpa only [δ₀, Nat.cast_prod] using A.divisor_isUnit δ₀ hδdiv)
  obtain ⟨D', hD', hND', hAD', φ, hφ, V, hred, hn, hft, hqc, hsep, U, hclass⟩ :=
    Arithmetic.AddedFromPure.exists_arithmetic_added_pel_fine_model_from_pureModel A P iota M hM Q hp3
      (A.divisor_isUnit N hNdiv) G (A.divisor_isUnit G.conductor hcdiv) hPresentations
  let A' := A.withDenominator D' hD'
  exact ⟨A', A'.divisor_isUnit N hND', p, hp, hp3, hpN, hpδ,
    A'.divisor_isUnit p (hpdiv.trans hAD'), V, hred, hn, hft, hqc, hsep, U, hclass⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsFromPureFactory
