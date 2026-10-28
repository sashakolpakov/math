import OAI.RepresentationTheory.Hecke.GaloisValuationCm
import OAI.NumberTheory.PadicHodge.Valuation
import OAI.RepresentationTheory.Hecke.GaloisValuationIntrinsic

/-! # Intrinsic Arithmetic -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic

noncomputable section

/-! The coefficient embedding, its normal Galois restriction, and the
q-adic valuation are constructed from field embeddings. The algebraic lifts
use the same complex embedding, preserving the RadialDilation polynomial identity.
These elementary bridges are isolated here to avoid importing unrelated
geometric statement modules through the broader CMExtraction development. -/

open scoped Classical
open OAI.NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter
abbrev Qbar := AlgebraicClosure ℚ
abbrev ComplexAlgebraics : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

instance complexAlgebraics_closed : IsAlgClosed ComplexAlgebraics :=
  (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
instance complexAlgebraics_algebraic : Algebra.IsAlgebraic ℚ ComplexAlgebraics :=
  algebraicClosure.isAlgebraic ℚ ℂ

def chosenClosureEquiv (j : Qbar →+* ℂ) : Qbar ≃ₐ[ℚ] ComplexAlgebraics := by
  let : IsAlgClosure ℚ Qbar := AlgebraicClosure.instIsAlgClosure ℚ
  let f : Qbar →ₐ[ℚ] ComplexAlgebraics := j.toRatAlgHom.codRestrict
    ComplexAlgebraics.toSubalgebra (fun a => mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom j.toRatAlgHom))
  let g : ComplexAlgebraics →ₐ[ℚ] Qbar := IsAlgClosed.lift
  exact AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective₂ f g).1

theorem chosenClosureEquiv_inverse (j : Qbar →+* ℂ) (a : ComplexAlgebraics) :
    j ((chosenClosureEquiv j).symm a) = (a : ℂ) :=
  congrArg (fun a : ComplexAlgebraics => (a : ℂ)) ((chosenClosureEquiv j).apply_symm_apply a)

def extendAlgebraicEmbedding {E F : Type} [Field E] [NumberField E]
    [Field F] [CharZero F] [IsAlgClosed F]
    (ιE : E →ₐ[ℚ] Qbar) (f : E →+* F) : Qbar →+* F := by
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : Algebra E Qbar := ιE.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ιE.commutes x).symm)
  let : Algebra.IsAlgebraic E Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let : Algebra E F := f.toAlgebra
  exact (IsAlgClosed.lift : Qbar →ₐ[E] F).toRingHom

theorem extendAlgebraicEmbedding_spec {E F : Type} [Field E] [NumberField E]
    [Field F] [CharZero F] [IsAlgClosed F]
    (ιE : E →ₐ[ℚ] Qbar) (f : E →+* F) (x : E) :
    extendAlgebraicEmbedding ιE f (ιE x) = f x := by
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : Algebra E Qbar := ιE.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ιE.commutes x).symm)
  let : Algebra.IsAlgebraic E Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let : Algebra E F := f.toAlgebra
  exact (IsAlgClosed.lift : Qbar →ₐ[E] F).commutes x

section Restriction
variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
def restriction (ι : E →ₐ[ℚ] Qbar) : Gal(Qbar/ℚ) →* Gal(E/ℚ) := by
  let : Algebra E Qbar := ι.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ι.commutes x).symm)
  exact AlgEquiv.restrictNormalHom E

omit [NumberField E] [NumberField.IsCMField E] in
theorem restriction_commutes (ι : E →ₐ[ℚ] Qbar) (σ : Gal(Qbar/ℚ)) (x : E) :
    σ (ι x) = ι ((restriction E ι σ) x) := by
  let : Algebra E Qbar := ι.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ι.commutes x).symm)
  exact (AlgEquiv.restrictNormal_commutes σ E x).symm

end Restriction

def globalValuation (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) (x : AlgebraicClosure ℚ) : ℚ :=
  NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι x)

lemma globalValuation_mul (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (x y : AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    globalValuation q ι (x * y) = globalValuation q ι x + globalValuation q ι y := by
  simpa only [globalValuation, map_mul] using
    NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_mul q (ι x) (ι y) ((map_ne_zero ι).mpr hx) ((map_ne_zero ι).mpr hy)

lemma globalValuation_add (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (x y : AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (globalValuation q ι x) (globalValuation q ι y) ≤ globalValuation q ι (x + y) := by
  have hxy' : ι x + ι y ≠ 0 := by simpa only [← map_add] using (map_ne_zero ι).mpr hxy
  simpa only [globalValuation, map_add] using
    NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_add q (ι x) (ι y) ((map_ne_zero ι).mpr hx) ((map_ne_zero ι).mpr hy) hxy'

lemma globalValuation_q (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) :
    globalValuation q ι (q : AlgebraicClosure ℚ) = 1 := by
  simpa only [globalValuation, map_natCast, Padic.valuation_p, Int.cast_one] using
    NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_algebraMap q (q : ℚ_[q])

def liftComplexAlgebraic (j : Qbar →+* ℂ) (z : ℂ) (hz : IsAlgebraic ℚ z) : Qbar :=
  (chosenClosureEquiv j).symm ⟨z, hz.isIntegral⟩

theorem liftComplexAlgebraic_image (j : Qbar →+* ℂ) (z : ℂ) (hz : IsAlgebraic ℚ z) :
    j (liftComplexAlgebraic j z hz) = z := chosenClosureEquiv_inverse j _

theorem finitePhase_isAlgebraic {z : ℂ} (hz : RadialDilation.Cm.finitePhase z) :
    IsAlgebraic ℚ z := by
  obtain ⟨n, hn, he⟩ := hz
  apply IsAlgebraic.of_pow hn
  rw [he]
  exact isAlgebraic_one

theorem unitCircle_all_conjugates (j : Qbar →+* ℂ) (a : Qbar)
    (ha : RadialDilation.Cm.algebraicUnitCircle (j a)) :
    ∀ σ : Gal(Qbar/ℚ), ‖j (σ a)‖ = 1 := by
  intro σ
  apply ha.2
  have he : minpoly ℚ (j a) = minpoly ℚ (σ a) :=
    (minpoly.algHom_eq j.toRatAlgHom j.injective a).trans (minpoly.algEquiv_eq σ a).symm
  rw [he]
  exact (Polynomial.aeval_algHom_apply j.toRatAlgHom (σ a) (minpoly ℚ (σ a))).trans
    (by rw [minpoly.aeval, map_zero])

theorem lift_dilation_parameters
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (j : Qbar →+* ℂ) (ιE : E →ₐ[ℚ] Qbar)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    (reps : Finset Gal(E/ℚ)) (r : Eˣ) (d : Gal(E/ℚ) → ℤ) (ε : ℤ)
    (ωc ζc : ℂ) (hζ : RadialDilation.Cm.finitePhase ζc)
    (hω : RadialDilation.Cm.algebraicUnitCircle ωc)
    (hrel : ωc ^ 2 = ζc * ∏ τ ∈ reps,
      (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (ε * 3 * d τ)) :
    ∃ ω ζ : Qbar, j ω = ωc ∧ j ζ = ζc ∧
      (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      ω ^ 2 = ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ) ∧
      ∀ σ : Gal(Qbar/ℚ), ‖j (σ ω)‖ = 1 := by
  let ω := liftComplexAlgebraic j ωc hω.1
  let ζ := liftComplexAlgebraic j ζc (finitePhase_isAlgebraic hζ)
  have hωj : j ω = ωc := liftComplexAlgebraic_image j ωc hω.1
  have hζj : j ζ = ζc := liftComplexAlgebraic_image j ζc _
  refine ⟨ω, ζ, hωj, hζj, ?_, ?_, unitCircle_all_conjugates j ω (hωj.symm ▸ hω)⟩
  · obtain ⟨n, hn, he⟩ := hζ
    refine ⟨n, hn, j.injective ?_⟩
    rw [map_pow, hζj, he, map_one]
  · apply j.injective
    rw [map_pow, hωj, map_mul, hζj]
    simp only [map_prod, map_zpow₀, hι]
    exact hrel

theorem root_all_conjugates_norm_one (j : Qbar →+* ℂ) (ω e₀ : Qbar)
    (M : ℕ) (hM : 0 < M) (hroot : e₀ ^ M = ω)
    (hω : ∀ σ : Gal(Qbar/ℚ), ‖j (σ ω)‖ = 1) :
    ∀ σ : Gal(Qbar/ℚ), ‖j (σ e₀)‖ = 1 := by
  intro σ
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').mp
  rw [← norm_pow, ← map_pow, ← map_pow, hroot, hω σ]

theorem lift_dilation_root
    (j : Qbar →+* ℂ) (ω : Qbar) (M : ℕ) (hM : 0 < M)
    (hω : ∀ σ : Gal(Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (e₀c ec : ℂ) (hroot : e₀c ^ M = j ω) (he : ec = e₀c ∨ ec = e₀c⁻¹) :
    ∃ e₀ e : Qbar, j e₀ = e₀c ∧ j e = ec ∧ e₀ ^ M = ω ∧
      (e = e₀ ∨ e = e₀⁻¹) ∧ ∀ σ : Gal(Qbar/ℚ), ‖j (σ e)‖ = 1 := by
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  have hωalg : IsAlgebraic ℚ (j ω) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ω).algHom j.toRatAlgHom
  have h₀alg : IsAlgebraic ℚ e₀c := IsAlgebraic.of_pow hM (hroot.symm ▸ hωalg)
  let e₀ := liftComplexAlgebraic j e₀c h₀alg
  have h₀j : j e₀ = e₀c := liftComplexAlgebraic_image j e₀c h₀alg
  have h₀pow : e₀ ^ M = ω := j.injective (by rw [map_pow, h₀j, hroot])
  have h₀unit := root_all_conjugates_norm_one j ω e₀ M hM h₀pow hω
  rcases he with rfl | rfl
  · exact ⟨e₀, e₀, h₀j, h₀j, h₀pow, Or.inl rfl, h₀unit⟩
  · refine ⟨e₀, e₀⁻¹, h₀j, ?_, h₀pow, Or.inr rfl, ?_⟩
    · rw [map_inv₀, h₀j]
    · intro σ
      rw [map_inv₀, map_inv₀, norm_inv, h₀unit σ, inv_one]

variable (q : ℕ) [Fact q.Prime]

def liftedSqrt (j : Qbar →+* ℂ) : Qbar :=
  liftComplexAlgebraic j (Real.sqrt (q : ℝ) : ℂ)
    (IsAlgebraic.of_pow (n := 2) (by decide) (by
      have h : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
        norm_cast
        exact Real.sq_sqrt (Nat.cast_nonneg _)
      rw [h]
      exact isAlgebraic_natCast q))

omit [Fact q.Prime] in
theorem liftedSqrt_image (j : Qbar →+* ℂ) :
    j (liftedSqrt q j) = (Real.sqrt (q : ℝ) : ℂ) := liftComplexAlgebraic_image j _ _

omit [Fact q.Prime] in
theorem liftedSqrt_sq (j : Qbar →+* ℂ) : (liftedSqrt q j) ^ 2 = (q : Qbar) := by
  apply j.injective
  rw [map_pow, liftedSqrt_image, map_natCast]
  norm_cast
  exact Real.sq_sqrt (Nat.cast_nonneg _)

theorem liftedSqrt_ne_zero (j : Qbar →+* ℂ) : liftedSqrt q j ≠ 0 := by
  intro h
  have hh := liftedSqrt_sq q j
  rw [h, zero_pow (by decide)] at hh
  exact (Fact.out : q.Prime).ne_zero (Nat.cast_eq_zero.mp hh.symm)

end

end OAI.RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic
