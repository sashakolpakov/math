import OAI.RepresentationTheory.Hecke.GaloisValuationCm
import OAI.NumberTheory.PadicHodge.Newton

/-! # Arithmetic -/

namespace OAI.NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter

noncomputable section

/-! The full recorded arithmetic input propositions, with only parser-level
renamings from FrobeniusSlope. No admitted statement is imported or used. -/

open scoped Classical TensorProduct

/-- The full FrobeniusSlope specification, not an assumed numerical Newton formula. -/
def FrobeniusSlopeInput : Prop := ∀
    {K L V : Type*}
    [Field K] [CharZero K]
    [Field L] [CharZero L] [IsAlgClosed L]
    [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V]
    (q : ℕ) (_hq : q.Prime)
    (jC : K →+* ℂ) (ι : K →+* L)
    (r b e : K)
    (_hr : r ^ 2 = (q : K))
    (_hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (_heC : ‖jC e‖ = 1)
    (_hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (Φ : Module.End L V)
    (T : Fin 3 → Module.End L V)

    -- Commuting pullbacks on the chosen summand.
    (_hcomm : ∀ i j, Commute (T i) (T j))
    (_hΦcomm : ∀ i, Commute Φ (T i))

    -- Equation (7), transported to contravariant H¹.
    (_hpoly :
      Φ ^ 3 - T 0 * Φ ^ 2 +
        q • (T 1 * Φ) - (q ^ 3) • T 2 = 0)

    -- Full generalized Hecke eigendata after absorbing C₀.
    (_hSatake :
      ∀ i : Fin 3,
        (T i).genEigenspace
          (ι ((![
            (q : K) * b * (r + r⁻¹ + e),
            (q : K) * b ^ 2 *
              (r * r⁻¹ + r * e + r⁻¹ * e),
            b ^ 3 * e
          ] : Fin 3 → K) i)) ⊤ = ⊤)

    -- Weil weights and characteristic-polynomial comparison.
    (_hWeil :
      ∀ a : K, Φ.HasEigenvalue (ι a) →
        ‖jC a‖ = Real.sqrt (q : ℝ))

    (ν : AddValuation L (WithTop ℚ))
    (_hνq : ν (q : L) = (1 : WithTop ℚ))
    (s : ℚ)
    (_hνe : ν (ι e) = (s : WithTop ℚ)),

    -- Generalized eigenspaces allow nonsemisimple Frobenius.
    Φ.genEigenspace (ι (b * r)) ⊤ = ⊤ ∧
      ∀ μ : L, Φ.HasEigenvalue μ →
        μ = ι (b * r) ∧
        ν μ = ((1 / 2 - s / 3 : ℚ) : WithTop ℚ)

open OAI.RepresentationTheory.Hecke.GaloisValuationCm in
/-- The full GaloisValuation specification, including every projective extension. -/
def GaloisValuationInput : Prop := ∀
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (ιE : E →ₐ[ℚ] RepresentationTheory.Hecke.GaloisValuationCm.Qbar)
    (res : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ) →* Gal(E/ℚ))
    (_hres : ∀ (σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ)) (x : E),
      σ (ιE x) = ιE ((res σ) x))
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hL2_8_normalized : v.val 1 = true)
    (d : Gal(E/ℚ) → ℤ)
    (_hL2_8_sign : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (reps : Finset (Gal(E/ℚ)))
    (_hL2_8_active : (1 : Gal(E/ℚ)) ∈ reps)
    (_hL2_8_representatives : ∀ τ : Gal(E/ℚ),
      τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (q : ℕ) (_hq : q.Prime)
    (M : ℕ) (_hM : 0 < M)
    (r : Eˣ)
    (_hnorm : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (ν : RepresentationTheory.Hecke.GaloisValuationCm.Qbar → ℚ)
    (_hν_mul : ∀ x y : RepresentationTheory.Hecke.GaloisValuationCm.Qbar, x ≠ 0 → y ≠ 0 →
      ν (x * y) = ν x + ν y)
    (_hν_add : ∀ x y : RepresentationTheory.Hecke.GaloisValuationCm.Qbar,
      x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (ν x) (ν y) ≤ ν (x + y))
    (_hν_q : ν (q : RepresentationTheory.Hecke.GaloisValuationCm.Qbar) = 1)
    (_hsplit : ∀ τ : Gal(E/ℚ),
      ν (ιE (τ (r : E))) =
        if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ)
        else if τ = 1 then -(M : ℚ)
        else 0)
    (e₀ e ω ζ : RepresentationTheory.Hecke.GaloisValuationCm.Qbar)
    (ε : ℤ) (_hC4_10_convention : ε = 1 ∨ ε = -1)
    (_hC4_10_phase : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (_hC4_10_relation : ω ^ 2 =
      ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ))
    (_hC4_11_root : e₀ ^ M = ω)
    (_hC4_11_parameter : e = e₀ ∨ e = e₀⁻¹)
    (j : RepresentationTheory.Hecke.GaloisValuationCm.Qbar →ₐ[ℚ] ℂ)
    (_hC4_10_unit : ∀ σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ), ‖j (σ e)‖ = 1)
    (s : RepresentationTheory.Hecke.GaloisValuationCm.Qbar) (_hs : s ^ 2 = (q : RepresentationTheory.Hecke.GaloisValuationCm.Qbar))
    (P : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ) → Fin 3 → RepresentationTheory.Hecke.GaloisValuationCm.Qbar)
    (_hE52 : ∀ σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ)
        (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s e i))),
    (ν e = (-3 / 2 : ℚ) ∨ ν e = (3 / 2 : ℚ)) ∧
    ∀ σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ),
      ν (σ e) = (d ((res σ)⁻¹) : ℚ) * ν e ∧
      (∃ eσ : RepresentationTheory.Hecke.GaloisValuationCm.Qbar,
        RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ) (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s eσ)) ∧
      (∀ eσ : RepresentationTheory.Hecke.GaloisValuationCm.Qbar,
        RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ) (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s eσ) →
          (eσ = σ e ∨ eσ = -(σ e)) ∧
          ν eσ = (d ((res σ)⁻¹) : ℚ) * ν e)

/-- Apply the full FrobeniusSlope proposition to the actual base-changed Frobenius.
The polynomial, Hecke eigenvalues and Weil bounds are its original antecedents;
the Newton-number formula is proved from the resulting eigenvalue valuations. -/
theorem newton_number_of_full_FrobeniusSlope
    (h_FrobeniusSlope : FrobeniusSlopeInput.{0, 0, 0})
    (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q]))
    [FiniteDimensional ℚ_[q] L]
    {D : Type} [AddCommGroup D] [Module L D] [FiniteDimensional L D]
    [Nontrivial D] [Module ℚ_[q] D] [IsScalarTower ℚ_[q] L D]
    (φ : D ≃ₗ[L] D)
    (jC : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (r b e : AlgebraicClosure ℚ)
    (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : jC r = (Real.sqrt (q : ℝ) : ℂ))
    (heC : ‖jC e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (T : Fin 3 → Module.End (AlgebraicClosure ℚ_[q])
      (AlgebraicClosure ℚ_[q] ⊗[L] D))
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hΦcomm : ∀ i, Commute (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (T i))
    (hpoly : let Φ := φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])
      Φ ^ 3 - T 0 * Φ ^ 2 + q • (T 1 * Φ) - (q ^ 3) • T 2 = 0)
    (hSatake : ∀ i : Fin 3,
      (T i).genEigenspace
        (ι ((![(q : AlgebraicClosure ℚ) * b * (r + r⁻¹ + e),
          (q : AlgebraicClosure ℚ) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
          b ^ 3 * e] : Fin 3 → AlgebraicClosure ℚ) i)) ⊤ = ⊤)
    (hWeil : ∀ a : AlgebraicClosure ℚ,
      Module.End.HasEigenvalue (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (ι a) →
        ‖jC a‖ = Real.sqrt (q : ℝ)) :
    (Padic.valuation (p := q) (LinearMap.det (φ.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
      (Module.finrank ℚ_[q] L : ℚ) * (Module.finrank L D : ℚ) *
        (1 / 2 - Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e) / 3) := by
  have he : e ≠ 0 := by
    intro he
    simp [he] at heC
  have hs := h_FrobeniusSlope q (Fact.out : q.Prime) jC ι r b e hr hrC heC hcentral
    (φ.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) T hcomm hΦcomm hpoly hSatake hWeil
    (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q) (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_q q)
    (Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι e))
    (Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_apply q (ι e) ((map_ne_zero ι).mpr he))
  exact Newton.CM.ExtremeSlopesAdapter.rational_newton_of_constant_slope q L φ _ (fun x hx => (hs.2 x hx).2)

/-- The valuation on algebraic global parameters obtained from the chosen
embedding into the p-adic algebraic closure. -/
def globalValuation (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) (x : AlgebraicClosure ℚ) : ℚ :=
  Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι x)

lemma globalValuation_mul (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (x y : AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    globalValuation q ι (x * y) = globalValuation q ι x + globalValuation q ι y := by
  simpa only [globalValuation, map_mul] using
    Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_mul q (ι x) (ι y) ((map_ne_zero ι).mpr hx) ((map_ne_zero ι).mpr hy)

lemma globalValuation_add (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (x y : AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (globalValuation q ι x) (globalValuation q ι y) ≤ globalValuation q ι (x + y) := by
  have hxy' : ι x + ι y ≠ 0 := by simpa only [← map_add] using (map_ne_zero ι).mpr hxy
  simpa only [globalValuation, map_add] using
    Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_add q (ι x) (ι y) ((map_ne_zero ι).mpr hx) ((map_ne_zero ι).mpr hy) hxy'

lemma globalValuation_q (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) :
    globalValuation q ι (q : AlgebraicClosure ℚ) = 1 := by
  simpa only [globalValuation, map_natCast, Padic.valuation_p, Int.cast_one] using
    Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_algebraMap q (q : ℚ_[q])

open OAI.RepresentationTheory.Hecke.GaloisValuationCm in
/-- Invoke FULL GaloisValuation with the proved canonical valuation interface.
Its rule holds for every normalized full extension of the projective parameter. -/
theorem signs_of_full_GaloisValuation
    (h_GaloisValuation : GaloisValuationInput)
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (ιE : E →ₐ[ℚ] RepresentationTheory.Hecke.GaloisValuationCm.Qbar)
    (res : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ) →* Gal(E/ℚ))
    (hres : ∀ (σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ)) (x : E),
      σ (ιE x) = ιE ((res σ) x))
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hLefschetzNormalization_normalized : v.val 1 = true)
    (d : Gal(E/ℚ) → ℤ)
    (hLefschetzNormalization_sign : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (reps : Finset (Gal(E/ℚ)))
    (_hL2_8_active : (1 : Gal(E/ℚ)) ∈ reps)
    (hLefschetzNormalization_representatives : ∀ τ : Gal(E/ℚ),
      τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (q : ℕ) [Fact q.Prime]
    (ι : RepresentationTheory.Hecke.GaloisValuationCm.Qbar →+* AlgebraicClosure ℚ_[q])
    (M : ℕ) (hM : 0 < M)
    (r : Eˣ)
    (_hnorm : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (hsplit : ∀ τ : Gal(E/ℚ),
      (globalValuation q ι) (ιE (τ (r : E))) =
        if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ)
        else if τ = 1 then -(M : ℚ)
        else 0)
    (e₀ e ω ζ : RepresentationTheory.Hecke.GaloisValuationCm.Qbar)
    (ε : ℤ) (hRadialDilation_convention : ε = 1 ∨ ε = -1)
    (hRadialDilation_phase : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hRadialDilation_relation : ω ^ 2 =
      ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ))
    (hSphericalAction_root : e₀ ^ M = ω)
    (hSphericalAction_parameter : e = e₀ ∨ e = e₀⁻¹)
    (j : RepresentationTheory.Hecke.GaloisValuationCm.Qbar →ₐ[ℚ] ℂ)
    (hRadialDilation_unit : ∀ σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ), ‖j (σ e)‖ = 1)
    (s : RepresentationTheory.Hecke.GaloisValuationCm.Qbar) (hs : s ^ 2 = (q : RepresentationTheory.Hecke.GaloisValuationCm.Qbar))
    (P : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ) → Fin 3 → RepresentationTheory.Hecke.GaloisValuationCm.Qbar)
    (hRationalStructure : ∀ σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ)
        (fun i => σ (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s e i))) :
    (globalValuation q ι e = -3 / 2 ∨ globalValuation q ι e = 3 / 2) ∧
    ∀ (σ : Gal(RepresentationTheory.Hecke.GaloisValuationCm.Qbar/ℚ)) (eσ : RepresentationTheory.Hecke.GaloisValuationCm.Qbar),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (P σ) (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s eσ) →
        globalValuation q ι eσ =
          (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (res σ)) : ℚ) * globalValuation q ι e := by
  have h := h_GaloisValuation E ιE res hres v hLefschetzNormalization_normalized d hLefschetzNormalization_sign reps
    _hL2_8_active hLefschetzNormalization_representatives q (Fact.out : q.Prime) M hM r _hnorm
    (globalValuation q ι) (globalValuation_mul q ι) (globalValuation_add q ι)
    (globalValuation_q q ι) hsplit e₀ e ω ζ ε hRadialDilation_convention hRadialDilation_phase
    hRadialDilation_relation hSphericalAction_root hSphericalAction_parameter j hRadialDilation_unit s hs P hRationalStructure
  refine ⟨h.1, ?_⟩
  intro σ eσ heσ
  have hv := ((h.2 σ).2.2 eσ heσ).2
  simpa only [hLefschetzNormalization_sign, inv_inv] using hv

end

end OAI.NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter
