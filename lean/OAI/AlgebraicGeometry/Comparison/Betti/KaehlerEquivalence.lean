import OAI.AlgebraicGeometry.Comparison.Betti.OneFormRealization

/-! # Kaehler Equivalence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.KaehlerEquivalence

noncomputable section

/-!
# Identification of the degree-one presentation with Kähler differentials

Both directions are constructed from the defining presentations. In particular,
injectivity of the realization is proved without imposing additional relations
or assuming the universal property for the constructed form quotient.
-/

universe u
variable (A : Type u) [CommRing A] [Algebra ℂ A]

def oneSymbol (a b : A) : Algebraic.Forms.Form A 1 := Algebraic.Forms.formSymbol A ![a, b]

omit [CommRing A] [Algebra ℂ A] in
@[simp]
theorem update_pair_zero (a b c : A) : Function.update ![a, b] 0 c = ![c, b] := by
  ext i
  fin_cases i <;> simp

omit [CommRing A] [Algebra ℂ A] in
@[simp]
theorem update_pair_one (a b c : A) : Function.update ![a, b] 1 c = ![a, c] := by
  ext i
  fin_cases i <;> simp

theorem oneSymbol_add_coeff (a b c : A) :
    oneSymbol A (a + b) c = oneSymbol A a c + oneSymbol A b c := by
  simpa [oneSymbol] using Algebraic.Forms.formSymbol_add A ![a, c] 0 a b

theorem oneSymbol_smul_coeff (a b : A) (c : ℂ) :
    oneSymbol A (c • a) b = c • oneSymbol A a b := by
  simpa [oneSymbol] using Algebraic.Forms.formSymbol_smul A ![a, b] 0 c a

theorem oneSymbol_add_diff (a b c : A) :
    oneSymbol A a (b + c) = oneSymbol A a b + oneSymbol A a c := by
  simpa [oneSymbol] using Algebraic.Forms.formSymbol_add A ![a, b] 1 b c

theorem oneSymbol_mul_diff (a b c : A) :
    oneSymbol A a (b * c) = oneSymbol A (a * b) c + oneSymbol A (a * c) b := by
  have h := (Submodule.Quotient.mk_eq_zero (Algebraic.Forms.relations A 1)).mpr
    (Submodule.subset_span (Algebraic.Forms.FormRelation.leibniz (A := A) 1 ![a, b] 0 b c))
  change (Algebraic.Forms.relations A 1).mkQ (_ - _ - _) = 0 at h
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  simpa [oneSymbol, Algebraic.Forms.formSymbol] using h

theorem oneSymbol_constant_diff (a : A) (c : ℂ) :
    oneSymbol A a (algebraMap ℂ A c) = 0 := by
  have h := (Submodule.Quotient.mk_eq_zero (Algebraic.Forms.relations A 1)).mpr
    (Submodule.subset_span (Algebraic.Forms.FormRelation.constant (A := A) 1 ![a, a] 0 c))
  simpa [oneSymbol, Algebraic.Forms.formSymbol] using h

def oneSymbolCoefficientMap (b : A) : A →ₗ[ℂ] Algebraic.Forms.Form A 1 where
  toFun a := oneSymbol A a b
  map_add' a c := oneSymbol_add_coeff A a c b
  map_smul' c a := oneSymbol_smul_coeff A a b c

/-- Send the finite sum ∑ aᵢ dbᵢ in the standard presentation to our symbols. -/
def kaehlerPresentationMap : (A →₀ A) →ₗ[ℂ] Algebraic.Forms.Form A 1 :=
  Finsupp.lsum ℂ (oneSymbolCoefficientMap A)

@[simp]
theorem kaehlerPresentationMap_single (a b : A) :
    kaehlerPresentationMap A (Finsupp.single b a) = oneSymbol A a b :=
  Finsupp.lsum_single _ _ _ _

theorem kaehlerPresentationMap_kills_relations {r : A →₀ A}
    (hr : r ∈ KaehlerDifferential.kerTotal ℂ A) : kaehlerPresentationMap A r = 0 := by
  have h : ∀ c : A, kaehlerPresentationMap A (c • r) = 0 := by
    induction hr using Submodule.span_induction with
    | mem r hr =>
        rcases hr with ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨x, rfl⟩)
        · intro c
          simp only [smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
            map_sub, map_add, kaehlerPresentationMap_single]
          rw [oneSymbol_add_diff, sub_self]
        · intro c
          simp only [smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
            map_sub, map_add, kaehlerPresentationMap_single]
          rw [oneSymbol_mul_diff, sub_self]
        · intro c
          simp only [Finsupp.smul_single, smul_eq_mul, mul_one,
            kaehlerPresentationMap_single, oneSymbol_constant_diff]
    | zero => intro c; simp
    | add r s hr hs ihr ihs =>
        intro c
        rw [smul_add, map_add, ihr c, ihs c, add_zero]
    | smul a r hr ihr =>
        intro c
        rw [smul_smul]
        exact ihr (c * a)
  simpa only [one_smul] using h 1

def kaehlerPresentationQuotientMap :
    ((A →₀ A) ⧸ (KaehlerDifferential.kerTotal ℂ A).restrictScalars ℂ) →ₗ[ℂ] Algebraic.Forms.Form A 1 :=
  ((KaehlerDifferential.kerTotal ℂ A).restrictScalars ℂ).liftQ
    (kaehlerPresentationMap A) (fun _ hr => kaehlerPresentationMap_kills_relations A hr)

/-- The inverse map uses the standard generators-and-relations theorem for Ω. -/
def kaehlerToOneForm : KaehlerDifferential ℂ A →ₗ[ℂ] Algebraic.Forms.Form A 1 :=
  (kaehlerPresentationQuotientMap A).comp
    (((Submodule.Quotient.restrictScalarsEquiv ℂ
      (KaehlerDifferential.kerTotal ℂ A)).symm.toLinearMap).comp
      ((KaehlerDifferential.quotKerTotalEquiv ℂ A).symm.toLinearMap.restrictScalars ℂ))

@[simp]
theorem kaehlerToOneForm_smul_D (a b : A) :
    kaehlerToOneForm A (a • KaehlerDifferential.D ℂ A b) = oneSymbol A a b := by
  change kaehlerPresentationQuotientMap A
    ((Submodule.Quotient.restrictScalarsEquiv ℂ
      (KaehlerDifferential.kerTotal ℂ A)).symm
      ((KaehlerDifferential.quotKerTotalEquiv ℂ A).symm
        (a • KaehlerDifferential.D ℂ A b))) = _
  rw [map_smul]
  have h := congrArg (fun D : Derivation ℂ A
      ((A →₀ A) ⧸ KaehlerDifferential.kerTotal ℂ A) => D b)
    (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D ℂ A)
  change (KaehlerDifferential.quotKerTotalEquiv ℂ A).symm
    (KaehlerDifferential.D ℂ A b) = _ at h
  rw [h]
  rw [KaehlerDifferential.derivationQuotKerTotal_apply,
    ← map_smul (KaehlerDifferential.kerTotal ℂ A).mkQ a (Finsupp.single b 1)]
  simp only [Submodule.mkQ_apply, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    kaehlerPresentationQuotientMap, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact kaehlerPresentationMap_single A a b

def oneFormKaehlerMap : Algebraic.Forms.Form A 1 →ₗ[ℂ] KaehlerDifferential ℂ A :=
  OneFormRealization.oneFormRealization (KaehlerDifferential.D ℂ A)

@[simp]
theorem oneFormKaehlerMap_oneSymbol (a b : A) :
    oneFormKaehlerMap A (oneSymbol A a b) = a • KaehlerDifferential.D ℂ A b := by
  exact OneFormRealization.oneFormRealization_symbol (KaehlerDifferential.D ℂ A) ![a, b]

theorem oneFormKaehler_leftInverse :
    Function.LeftInverse (kaehlerToOneForm A) (oneFormKaehlerMap A) := by
  intro x
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A 1).mkQ_surjective x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single a c =>
      have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
      have hc : Finsupp.single a c = c • Algebraic.Forms.symbol A a := by simp [Algebraic.Forms.symbol]
      rw [hc]
      simp only [map_smul]
      apply congrArg (c • ·)
      change kaehlerToOneForm A (oneFormKaehlerMap A (Algebraic.Forms.formSymbol A a)) = Algebraic.Forms.formSymbol A a
      rw [ha]
      change kaehlerToOneForm A (oneFormKaehlerMap A (oneSymbol A (a 0) (a 1))) = _
      rw [oneFormKaehlerMap_oneSymbol, kaehlerToOneForm_smul_D]
      rfl

theorem oneFormKaehler_rightInverse :
    Function.RightInverse (kaehlerToOneForm A) (oneFormKaehlerMap A) := by
  intro x
  obtain ⟨r, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ A x
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s ihr ihs => simp only [map_add, ihr, ihs]
  | single b a => simp only [Finsupp.linearCombination_single,
      kaehlerToOneForm_smul_D, oneFormKaehlerMap_oneSymbol]

/-- The degree-one algebraic form space is the actual Kähler differential module. -/
def oneFormsKaehlerEquiv : Algebraic.Forms.Form A 1 ≃ₗ[ℂ] KaehlerDifferential ℂ A :=
  { oneFormKaehlerMap A with
    invFun := kaehlerToOneForm A
    left_inv := oneFormKaehler_leftInverse A
    right_inv := oneFormKaehler_rightInverse A }

end

end OAI.AlgebraicGeometry.Comparison.Betti.KaehlerEquivalence
