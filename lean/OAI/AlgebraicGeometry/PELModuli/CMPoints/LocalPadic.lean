import OAI.AlgebraicGeometry.PELModuli.CMPoints.Splitting
import OAI.NumberTheory.Splitting.Integral
import OAI.NumberTheory.Splitting.Polynomial

/-! # Local Padic -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

noncomputable section

section

/-! Construct q-adic embeddings from simple residue roots, using Hensel's
lemma for the actual q-adic integers and an integral primitive element. -/

open _root_.Polynomial _root_.NumberField

variable {q : ℕ} [Fact q.Prime]

theorem toZMod_eq_zero_iff_norm_lt_one (z : PadicInt q) :
    PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  change z ∈ RingHom.ker PadicInt.toZMod ↔ _
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem polynomial_reduction_eval (f : ℤ[X]) (z : PadicInt q) :
    PadicInt.toZMod (f.aeval z) =
      (f.map (Int.castRingHom (ZMod q))).eval (PadicInt.toZMod z) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval_map]
  congr 1
  ext n
  simp

/-- A simple residue root lifts to an actual q-adic integral root. -/
theorem hensel_lift_simple_root (f : ℤ[X]) (r : ZMod q)
    (hr : (f.map (Int.castRingHom (ZMod q))).eval r = 0)
    (hd : ((f.map (Int.castRingHom (ZMod q))).derivative).eval r ≠ 0) :
    ∃ z : PadicInt q, f.aeval z = 0 ∧ PadicInt.toZMod z = r := by
  let a : PadicInt q := r.val
  have ha : PadicInt.toZMod a = r := by simp [a]
  have hf : ‖f.aeval a‖ < 1 :=
    (toZMod_eq_zero_iff_norm_lt_one _).mp (by rw [polynomial_reduction_eval, ha, hr])
  have hd' : ‖f.derivative.aeval a‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt _)
    intro h
    have hz := (toZMod_eq_zero_iff_norm_lt_one _).mpr h
    rw [polynomial_reduction_eval, ha, ← Polynomial.derivative_map] at hz
    exact hd hz
  obtain ⟨z, hz, hza, _⟩ := hensels_lemma (F := f) (a := a) (by
    simpa only [hd', one_pow] using hf)
  refine ⟨z, hz, ?_⟩
  have he : PadicInt.toZMod (z - a) = 0 :=
    (toZMod_eq_zero_iff_norm_lt_one _).mpr (by simpa only [hd'] using hza)
  rwa [map_sub, sub_eq_zero, ha] at he

/-- Algebraic integers remain integral under every embedding in Q_q. -/
def integersToPadicInt {K : Type*} [Field K] [NumberField K]
    (f : K →+* Padic q) : RingOfIntegers K →+* PadicInt q := by
  have hi (a : RingOfIntegers K) : IsIntegral (PadicInt q) (f (a : K)) :=
    ((a.property.map f.toIntAlgHom).tower_top)
  let z (a : RingOfIntegers K) : PadicInt q :=
    (IsIntegrallyClosed.isIntegral_iff.mp (hi a)).choose
  have hz (a : RingOfIntegers K) : (z a : Padic q) = f (a : K) :=
    (IsIntegrallyClosed.isIntegral_iff.mp (hi a)).choose_spec
  exact {
    toFun := z
    map_one' := by apply Subtype.ext; rw [hz]; exact map_one f
    map_zero' := by apply Subtype.ext; rw [hz]; exact map_zero f
    map_add' := by intro a b; apply Subtype.ext; simp only [PadicInt.coe_add, hz]; exact map_add f _ _
    map_mul' := by intro a b; apply Subtype.ext; simp only [PadicInt.coe_mul, hz]; exact map_mul f _ _ }

theorem integersToPadicInt_coe {K : Type*} [Field K] [NumberField K]
    (f : K →+* Padic q) (a : RingOfIntegers K) :
    (integersToPadicInt f a : Padic q) = f (a : K) :=
  (IsIntegrallyClosed.isIntegral_iff.mp
    ((a.property.map f.toIntAlgHom).tower_top : IsIntegral (PadicInt q) (f (a : K)))).choose_spec

/-- Lift a simple integral primitive-element residue to a field embedding. -/
theorem exists_padic_embedding_of_simple_residue
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K) (hint : IsIntegral ℤ B.gen)
    (r : RingOfIntegers K →+* ZMod q)
    (hsep : ((minpoly ℤ (⟨B.gen, hint⟩ : RingOfIntegers K)).map
      (Int.castRingHom (ZMod q))).Separable) : Nonempty (K →+* Padic q) := by
  let θ : RingOfIntegers K := ⟨B.gen, hint⟩
  let f : ℤ[X] := minpoly ℤ θ
  have hr : (f.map (Int.castRingHom (ZMod q))).eval (r θ) = 0 := by
    rw [Polynomial.eval_map]
    change aeval (r.toIntAlgHom θ) f = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hd : (f.map (Int.castRingHom (ZMod q))).derivative.eval (r θ) ≠ 0 :=
    hsep.eval₂_derivative_ne_zero (RingHom.id _) hr
  obtain ⟨z, hz, _⟩ := hensel_lift_simple_root f (r θ) hr hd
  have hz' : aeval (z : Padic q) f = 0 := by
    have h := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom ℤ (PadicInt q) (Padic q)) z f
    exact h.trans (congrArg (algebraMap (PadicInt q) (Padic q)) hz |>.trans (map_zero _))
  have hmin : minpoly ℚ B.gen = f.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral
  have hroot : aeval (z : Padic q) (minpoly ℚ B.gen) = 0 := by
    rw [hmin, Polynomial.aeval_map_algebraMap]
    exact hz'
  exact ⟨(B.lift (z : Padic q) hroot).toRingHom⟩

/-- Outside one finite bound, complete splitting supplies an actual embedding
of the number field into Q_q. -/
theorem exists_padic_embedding_bound (K : Type*) [Field K] [NumberField K] :
    ∃ d : ℕ, ∀ (q : ℕ) [Fact q.Prime], d < q → Arithmetic.SplitsCompletelyAt K q →
      Nonempty (K →+* Padic q) := by
  obtain ⟨B, hint⟩ := NumberTheory.Splitting.Integral.SplitPrimesConstruction.exists_integral_powerBasis K
  let θ : RingOfIntegers K := ⟨B.gen, hint⟩
  let f := minpoly ℤ θ
  have hf : f.natDegree ≠ 0 := (minpoly.natDegree_pos θ.isIntegral).ne'
  have hsep : (f.map (Int.castRingHom ℚ)).Separable := by
    have h := Algebra.IsSeparable.isSeparable ℚ B.gen
    change (minpoly ℚ (algebraMap (RingOfIntegers K) K θ)).Separable at h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral] at h
    exact h
  obtain ⟨d, hd, hgood⟩ := NumberTheory.Splitting.Polynomial.SplitPrimesConstruction.exists_separability_denominator f hf hsep
  refine ⟨d.natAbs, fun q _ hq hs => ?_⟩
  obtain ⟨e⟩ := hs
  let i : Fin (Module.finrank ℚ K) := ⟨0, Module.finrank_pos⟩
  let r := (Pi.evalRingHom (fun _ : Fin (Module.finrank ℚ K) => ZMod q) i).comp
    (e.toRingHom.comp (Ideal.Quotient.mk _))
  apply exists_padic_embedding_of_simple_residue B hint r
  apply hgood q (Fact.out : q.Prime)
  intro hdiv
  have hn : q ∣ d.natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdiv
  exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hd) hq) hn

end

section

/-! The finite place defined by an actual embedding into Q_q. Its adic
topology agrees with the topology pulled back from Q_q. -/

open _root_.NumberField IsDedekindDomain
open scoped NNReal

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]

def embeddingResidue (f : K →+* Padic q) : RingOfIntegers K →+* ZMod q :=
  PadicInt.toZMod.comp (integersToPadicInt f)

def embeddingPlace (f : K →+* Padic q) : HeightOneSpectrum (RingOfIntegers K) where
  asIdeal := RingHom.ker (embeddingResidue f)
  isPrime := RingHom.ker_isPrime _
  ne_bot := by
    intro h
    have hm : (q : RingOfIntegers K) ∈ RingHom.ker (embeddingResidue f) := by
      rw [RingHom.mem_ker, map_natCast]
      exact ZMod.natCast_self q
    rw [h, Ideal.mem_bot] at hm
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hm

theorem embeddingPlace_liesOver (f : K →+* Padic q) :
    (q : RingOfIntegers K) ∈ (embeddingPlace f).asIdeal := by
  change embeddingResidue f q = 0
  simp

theorem embedding_norm_eq_one_of_not_mem (f : K →+* Padic q) (a : RingOfIntegers K)
    (ha : a ∉ (embeddingPlace f).asIdeal) : ‖f (a : K)‖ = 1 := by
  rw [← integersToPadicInt_coe f a]
  change ‖integersToPadicInt f a‖ = 1
  apply le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt _)
  intro h
  exact ha ((toZMod_eq_zero_iff_norm_lt_one _).mpr h)

/-- The normalized adic valuation and the pulled-back q-adic norm have
the same valuation ring, hence define equivalent valuations. -/
theorem embedding_valuation_equiv (f : K →+* Padic q) :
    ((embeddingPlace f).valuation K).IsEquiv
      ((NormedField.valuation (K := Padic q)).comap f) := by
  let v := embeddingPlace f
  let w := (NormedField.valuation (K := Padic q)).comap f
  have hle : HeightOneSpectrum.valuationSubringAtPrime K v ≤ w.valuationSubring := by
    rintro x ⟨a, s, hs, rfl⟩
    have hn : ‖f (s : K)‖ = 1 := embedding_norm_eq_one_of_not_mem f s hs
    have ha : ‖f (a : K)‖ ≤ 1 := by
      rw [← integersToPadicInt_coe f a]
      exact (integersToPadicInt f a).property
    change ‖f ((a : K) * (s : K)⁻¹)‖₊ ≤ 1
    rw [← div_eq_mul_inv, map_div₀, nnnorm_div]
    have hn' : ‖f (s : K)‖₊ = 1 := NNReal.coe_injective hn
    rw [hn', div_one]
    exact ha
  have htop : w.valuationSubring ≠ ⊤ := by
    intro h
    have hm : ((q : K)⁻¹) ∈ w.valuationSubring := by rw [h]; trivial
    change ‖f (q : K)⁻¹‖₊ ≤ 1 at hm
    have hm' : ‖f (q : K)⁻¹‖ ≤ 1 := hm
    rw [map_inv₀, map_natCast, norm_inv, Padic.norm_p, inv_inv] at hm'
    exact (not_le_of_gt (Nat.one_lt_cast.mpr (Fact.out : q.Prime).one_lt)) hm'
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact ValuationSubring.eq_of_le_of_ne_top _ hle htop

/-- The embedding induces exactly the uniformity of the selected finite place. -/
theorem embedding_isUniformInducing (f : K →+* Padic q) :
    IsUniformInducing (f.comp (WithVal.equiv ((embeddingPlace f).valuation K)).toRingHom) := by
  let : NormedField K := NormedField.induced K (Padic q) f f.injective
  have hi : Isometry f := by intro x y; rfl
  let : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
      intro x y
      change ‖f (x + y)‖ ≤ max ‖f x‖ ‖f y‖
      rw [map_add]
      exact Padic.nonarchimedean _ _)
  let : Valued K ℝ≥0 := NormedField.toValued
  let e := WithVal.uniformEquiv (R := K)
    (show Valued.v = ((NormedField.valuation (K := Padic q)).comap f) from rfl)
    (embedding_valuation_equiv f)
  exact hi.isUniformInducing.comp e.isUniformInducing

theorem embedding_denseRange (f : K →+* Padic q) :
    DenseRange (f.comp (WithVal.equiv ((embeddingPlace f).valuation K)).toRingHom) := by
  apply (Padic.denseRange_ratCast q).mono
  rintro y ⟨a, rfl⟩
  exact ⟨(WithVal.equiv ((embeddingPlace f).valuation K)).symm (a : K),
    by simp⟩

end

section

/-! Identify the actual adic completion with Q_q using the dense uniform
embedding constructed from the field embedding. -/

open _root_.NumberField IsDedekindDomain UniformSpace

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]

def embeddingCompletionHom (f : K →+* Padic q) :
    (embeddingPlace f).adicCompletion K →+* Padic q :=
  (Completion.extensionHom
    (f.comp (WithVal.equiv ((embeddingPlace f).valuation K)).toRingHom)
    (embedding_isUniformInducing f).uniformContinuous.continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K (embeddingPlace f)).toRingHom

theorem embeddingCompletionHom_coe (f : K →+* Padic q) (x : K) :
    embeddingCompletionHom f (FinitePlace.embedding (embeddingPlace f) x) = f x := by
  change Completion.extensionHom _ (embedding_isUniformInducing f).uniformContinuous.continuous
    ((HeightOneSpectrum.adicCompletion.equiv K (embeddingPlace f))
      ((HeightOneSpectrum.adicCompletion.equiv K (embeddingPlace f)).symm
        ((WithVal.equiv ((embeddingPlace f).valuation K)).symm x :
          ((embeddingPlace f).valuation K).Completion))) = f x
  rw [RingEquiv.apply_symm_apply, Completion.extensionHom_coe]
  exact congrArg f ((WithVal.equiv ((embeddingPlace f).valuation K)).apply_symm_apply x)

theorem embeddingCompletionHom_isUniformInducing (f : K →+* Padic q) :
    IsUniformInducing (embeddingCompletionHom f) :=
  (Completion.isUniformInducing_extension (embedding_isUniformInducing f)).comp
    (HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion K (embeddingPlace f))

theorem embeddingCompletionHom_denseRange (f : K →+* Padic q) :
    DenseRange (embeddingCompletionHom f) := by
  apply (embedding_denseRange f).mono
  rintro y ⟨x, rfl⟩
  exact ⟨FinitePlace.embedding (embeddingPlace f)
    ((WithVal.equiv ((embeddingPlace f).valuation K)) x), embeddingCompletionHom_coe f _⟩

theorem embeddingCompletionHom_bijective (f : K →+* Padic q) :
    Function.Bijective (embeddingCompletionHom f) := by
  refine ⟨(embeddingCompletionHom f).injective, ?_⟩
  apply Set.range_eq_univ.mp
  have hclosed := (embeddingCompletionHom_isUniformInducing f).isComplete_range.isClosed
  exact hclosed.closure_eq.symm.trans (embeddingCompletionHom_denseRange f).closure_range

/-- The ring equivalence is constructed by extending the given embedding. -/
def embeddingCompletionEquiv (f : K →+* Padic q) :
    (embeddingPlace f).adicCompletion K ≃+* Padic q :=
  RingEquiv.ofBijective (embeddingCompletionHom f) (embeddingCompletionHom_bijective f)

theorem embeddingCompletionEquiv_continuous (f : K →+* Padic q) :
    Continuous (embeddingCompletionEquiv f) :=
  (embeddingCompletionHom_isUniformInducing f).uniformContinuous.continuous

theorem embeddingCompletionEquiv_symm_continuous (f : K →+* Padic q) :
    Continuous (embeddingCompletionEquiv f).symm :=
  ((embeddingCompletionEquiv f).toEquiv.toHomeomorphOfIsInducing
    (embeddingCompletionHom_isUniformInducing f).isInducing).continuous_symm

theorem embeddingCompletionEquiv_comp (f : K →+* Padic q) :
    (embeddingCompletionEquiv f).toRingHom.comp
      (FinitePlace.embedding (embeddingPlace f)) = f := by
  ext x
  exact embeddingCompletionHom_coe f x

end

/-! Construct all fields of the literal q-adic choice, including the two
algebraic-closure embeddings and the compatible completion identification. -/

open _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]

/-- Extend the chosen complex and q-adic embeddings through a common
algebraic closure of Q. -/
def qadicChoiceOfEmbedding (κ : K →+* ℂ) (f : K →+* Padic q) : Arithmetic.QadicChoice K κ q := by
  letI : Algebra ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instAlgebra ℚ
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ψ : K →+* AlgebraicClosure ℚ :=
    (IsAlgClosed.lift : K →ₐ[ℚ] AlgebraicClosure ℚ).toRingHom
  letI : Algebra K (AlgebraicClosure ℚ) := ψ.toAlgebra
  letI : IsScalarTower ℚ K (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change (r : AlgebraicClosure ℚ) = ψ (r : K)
      simp)
  letI : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) K
  letI : Algebra K ℂ := κ.toAlgebra
  let c : AlgebraicClosure ℚ →ₐ[K] ℂ := IsAlgClosed.lift
  let fq : K →+* AlgebraicClosure (Padic q) :=
    (algebraMap (Padic q) (AlgebraicClosure (Padic q))).comp f
  letI : Algebra K (AlgebraicClosure (Padic q)) := fq.toAlgebra
  let i : AlgebraicClosure ℚ →ₐ[K] AlgebraicClosure (Padic q) := IsAlgClosed.lift
  refine {
    complexClosure := c.toRingHom
    fieldInClosure := ψ
    complex_compatibility := ?_
    iota := i.toRingHom
    prime := embeddingPlace f
    liesOver := embeddingPlace_liesOver f
    completion := embeddingCompletionEquiv f
    completion_continuous := embeddingCompletionEquiv_continuous f
    completion_inverse_continuous := embeddingCompletionEquiv_symm_continuous f
    closure_compatibility := ?_
    integralEmbedding := integersToPadicInt f
    integral_compatibility := ?_ }
  · ext x
    exact c.commutes x
  · rw [embeddingCompletionEquiv_comp]
    ext x
    exact i.commutes x
  · rw [embeddingCompletionEquiv_comp]
    ext x
    exact integersToPadicInt_coe f x

/-- A sufficiently large completely split prime admits the full q-adic choice. -/
theorem exists_qadicChoice_bound (κ : K →+* ℂ) :
    ∃ d : ℕ, ∀ (q : ℕ) [Fact q.Prime], d < q → Arithmetic.SplitsCompletelyAt K q →
      Nonempty (Arithmetic.QadicChoice K κ q) := by
  obtain ⟨d, hd⟩ := exists_padic_embedding_bound K
  refine ⟨d, fun q _ hq hs => ?_⟩
  obtain ⟨f⟩ := hd q hq hs
  exact ⟨qadicChoiceOfEmbedding κ f⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic
