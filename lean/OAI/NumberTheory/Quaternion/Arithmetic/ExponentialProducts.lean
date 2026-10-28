import OAI.NumberTheory.Quaternion.Arithmetic.OrderedProductDerivative
import OAI.NumberTheory.Quaternion.Arithmetic.SpanLocal

/-! # Exponential Products -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ExponentialProducts

noncomputable section

/-! Ordered products of local one-parameter families. Their derivative is
the sum of the chosen directions, and small integral parameters stay in a
closed submonoid containing the original exponential elements. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

attribute [local instance] TangentBracket.finiteClosedPrimeNontriviallyNormedField
attribute [local instance 50] OrderedProductDerivative.finitePrimeNormedAlgebra

variable {F : Type} [Field F] [NumberField F]

def finiteExpProduct (v : HeightOneSpectrum (𝓞 F))
    {A E : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A]
    [NormedAddCommGroup E] [NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) E]
    {n : ℕ} (L : Fin n → E →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)]
      TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (X : Fin n → A) : E → A :=
  fun x => ((List.finRange n).map (fun i => NormedSpace.exp (L i x • X i))).prod

theorem finiteExpProduct_zero (v : HeightOneSpectrum (𝓞 F))
    {A E : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A]
    [NormedAddCommGroup E] [NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) E]
    {n : ℕ} (L : Fin n → E →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)]
      TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (X : Fin n → A) :
    finiteExpProduct v L X 0 = 1 := by
  unfold finiteExpProduct
  apply OrderedProductDerivative.orderedProduct_eq_one (f := fun i x => NormedSpace.exp (L i x • X i))
  intro i _
  simp only [map_zero, zero_smul, NormedSpace.exp_zero]

theorem finiteExpProduct_hasStrictFDerivAt (v : HeightOneSpectrum (𝓞 F))
    {A E : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) E]
    {n : ℕ} (L : Fin n → E →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)]
      TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (X : Fin n → A) :
    HasStrictFDerivAt (finiteExpProduct v L X) (∑ i, (L i).smulRight (X i)) 0 := by
  rw [Fin.sum_univ_def]
  apply OrderedProductDerivative.hasStrictFDerivAt_orderedProduct_one
  · intro i _
    have he : HasStrictFDerivAt (NormedSpace.exp : A → A)
        (ContinuousLinearMap.id (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A)
        ((L i).smulRight (X i) 0) := by
      rw [map_zero]
      exact OrderedProductDerivative.finiteExp_hasStrictFDerivAt_prime v A
    convert! he.comp (0 : E) ((L i).smulRight (X i)).hasStrictFDerivAt using 1
  · intro i _
    simp only [map_zero, zero_smul, NormedSpace.exp_zero]

theorem finiteExpProduct_eventually_mem (v : HeightOneSpectrum (𝓞 F))
    {A E : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) E]
    {n : ℕ} (L : Fin n → E →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)]
      TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (X : Fin n → A)
    (H : Submonoid A) (hH : IsClosed (H : Set A))
    (hX : ∀ i, X i ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius)
    (heX : ∀ i, NormedSpace.exp (X i) ∈ H) :
    ∀ᶠ x in 𝓝 (0 : E), finiteExpProduct v L X x ∈ H := by
  have hL : ∀ i, ∀ᶠ x in 𝓝 (0 : E), L i x ∈ PrimeLocalIntegral.primeIntegerRing v := by
    intro i
    have h := (L i).continuous.tendsto 0
    rw [map_zero] at h
    exact h ((PrimeLocalIntegral.primeIntegerRing_isOpen v).mem_nhds (PrimeLocalIntegral.primeIntegerRing v).zero_mem)
  filter_upwards [eventually_all.mpr hL] with x hx
  apply H.list_prod_mem
  intro y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
  have hi : (L i x : v.adicCompletion F) ∈ PrimeLocalIntegral.integralPrimeScalars v := hx i
  exact PrimeLocalIntegral.finite_exp_smul_mem_closed_submonoid v H hH (hX i) (heX i) hi

end

end OAI.NumberTheory.Quaternion.Arithmetic.ExponentialProducts
