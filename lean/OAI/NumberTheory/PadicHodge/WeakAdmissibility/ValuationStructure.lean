import OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisCoefficients

/-! # Valuation Structure -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisD
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DcrisCoefficients
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm
section

/-! The actual maximal-unramified scalar field and its Frobenius on D_cris. -/

variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [Module.Finite ℚ_[p] K]

def k0ModelEquiv : ResidueCoefficientField.ResidueCoefficient p K ≃ₐ[ℚ_[p]] MaximalUnramified.K0 p K :=
  AlgebraicCoefficientFields.coefficientSubfieldEquiv p (FiniteFieldResidue.residueEmbedding p K)

instance k0Finite : Module.Finite ℚ_[p] (MaximalUnramified.K0 p K) :=
  AlgebraicCoefficientFields.coefficientSubfield_finite p (FiniteFieldResidue.residueEmbedding p K)

def k0Frobenius : MaximalUnramified.K0 p K ≃ₐ[ℚ_[p]] MaximalUnramified.K0 p K :=
  (k0ModelEquiv p K).symm.trans
    ((CoefficientComparison.coefficientFrobeniusAlg p (FiniteFieldResidue.residueEmbedding p K)).trans (k0ModelEquiv p K))

theorem k0Frobenius_model (a : ResidueCoefficientField.ResidueCoefficient p K) :
    k0Frobenius p K (k0ModelEquiv p K a) = k0ModelEquiv p K (UnramifiedCoefficients.coefficientFrobenius (p := p) a) := by
  simp only [k0Frobenius, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rfl

theorem k0Frobenius_period (a : MaximalUnramified.K0 p K) :
    (k0Frobenius p K)^[Module.finrank ℚ_[p] (MaximalUnramified.K0 p K)] a = a := by
  rw [MaximalUnramified.K0_finrank]
  have hs : Function.Semiconj (k0ModelEquiv p K) (UnramifiedCoefficients.coefficientFrobenius (p := p)) (k0Frobenius p K) :=
    fun x => (k0Frobenius_model p K x).symm
  have he := hs.iterate_right (UnramifiedCoefficients.residueDegree (p := p) (k := FiniteFieldResidue.FieldResidue p K)) ((k0ModelEquiv p K).symm a)
  rw [UnramifiedCoefficients.coefficientFrobenius_period, AlgEquiv.apply_symm_apply] at he
  exact he.symm

theorem k0Frobenius_model_symm (a : MaximalUnramified.K0 p K) :
    (k0ModelEquiv p K).symm (k0Frobenius p K a) =
      UnramifiedCoefficients.coefficientFrobenius (p := p) ((k0ModelEquiv p K).symm a) := by
  have he := k0Frobenius_model p K ((k0ModelEquiv p K).symm a)
  rw [AlgEquiv.apply_symm_apply] at he
  rw [he, AlgEquiv.symm_apply_apply]

def k0ToBCris : MaximalUnramified.K0 p K →ₐ[ℚ_[p]] Logarithm.PeriodRings.BCris p :=
  (CoefficientComparison.coefficientFieldToBCrisAlg p (FiniteFieldResidue.residueEmbedding p K)).comp (k0ModelEquiv p K).symm.toAlgHom

instance k0PeriodAlgebra : Algebra (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) := (k0ToBCris p K).toRingHom.toAlgebra

instance k0PeriodSMul : SMul (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) := ⟨fun a x => k0ToBCris p K a * x⟩

instance k0PeriodModule : Module (MaximalUnramified.K0 p K) (Logarithm.PeriodRings.BCris p) := Algebra.toModule

theorem k0ToBCris_fixed (σ : K.fixingSubgroup) (a : MaximalUnramified.K0 p K) :
    Galois.galoisBCrisMap p σ.val (k0ToBCris p K a) = k0ToBCris p K a :=
  ResidueCoefficientField.coefficientBCris_fixed p K σ ((k0ModelEquiv p K).symm a)

theorem k0ToBCris_frobenius (a : MaximalUnramified.K0 p K) :
    Logarithm.bCrisFrobenius p (k0ToBCris p K a) = k0ToBCris p K (k0Frobenius p K a) := by
  have he := k0Frobenius_model p K ((k0ModelEquiv p K).symm a)
  rw [AlgEquiv.apply_symm_apply] at he
  rw [he]
  change Logarithm.bCrisFrobenius p (UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) ((k0ModelEquiv p K).symm a)) =
    UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K)
      ((k0ModelEquiv p K).symm (k0ModelEquiv p K (UnramifiedCoefficients.coefficientFrobenius (p := p) ((k0ModelEquiv p K).symm a))))
  rw [AlgEquiv.symm_apply_apply, UnramifiedCoefficients.coefficientFieldToBCris_frobenius]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

instance dCrisK0SMul (ρ : Representation ℚ_[p] K.fixingSubgroup V) : SMul (MaximalUnramified.K0 p K) (DcrisD.Dcris p K ρ) :=
  ⟨fun a x => (k0ModelEquiv p K).symm a • x⟩

instance dCrisK0Module (ρ : Representation ℚ_[p] K.fixingSubgroup V) : Module (MaximalUnramified.K0 p K) (DcrisD.Dcris p K ρ) :=
  Module.compHom (DcrisD.Dcris p K ρ) (k0ModelEquiv p K).symm.toRingHom

theorem dCrisFrobenius_k0_semilinear (ρ : Representation ℚ_[p] K.fixingSubgroup V)
    (a : MaximalUnramified.K0 p K) (x : DcrisD.Dcris p K ρ) :
    DcrisD.dCrisFrobenius p K ρ (a • x) = k0Frobenius p K a • DcrisD.dCrisFrobenius p K ρ x := by
  change DcrisD.dCrisFrobenius p K ρ ((k0ModelEquiv p K).symm a • x) =
    (k0ModelEquiv p K).symm (k0Frobenius p K a) • DcrisD.dCrisFrobenius p K ρ x
  exact (DcrisCoefficients.dCrisFrobenius_semilinear p K ρ _ x).trans
    (congrArg (fun b : ResidueCoefficientField.ResidueCoefficient p K => b • DcrisD.dCrisFrobenius p K ρ x)
      (k0Frobenius_model_symm p K a).symm)

end

/-! The actual rational-valued additive valuation on K0, normalized by v(p)=1. -/

def naturalToRationalTop : ℕ∞ →+ WithTop ℚ := (Nat.castAddMonoidHom ℚ).withTopMap

theorem naturalToRationalTop_monotone : Monotone naturalToRationalTop := by
  intro a b hab
  cases a using WithTop.recTopCoe with
  | top =>
    have hb : b = ⊤ := top_le_iff.mp hab
    rw [hb]
    exact le_rfl
  | coe a =>
    cases b using WithTop.recTopCoe with
    | top => exact le_top
    | coe b =>
      change ((a : ℚ) : WithTop ℚ) ≤ ((b : ℚ) : WithTop ℚ)
      exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (WithTop.coe_le_coe.mp hab))

theorem naturalToRationalTop_eq_top (a : ℕ∞) : naturalToRationalTop a = ⊤ ↔ a = ⊤ := by
  change WithTop.map (fun n : ℕ => (n : ℚ)) a = ⊤ ↔ a = ⊤
  cases a using WithTop.recTopCoe with
  | top => simp only [WithTop.map_top, true_iff]; rfl
  | coe a =>
    rw [WithTop.map_coe]
    exact iff_of_false WithTop.coe_ne_top (ENat.natCast_ne_top a)

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

def wittIntegerValuation : AddValuation (WittVector p k) (WithTop ℚ) :=
  (IsDiscreteValuationRing.addVal (WittVector p k)).map naturalToRationalTop rfl naturalToRationalTop_monotone

theorem wittIntegerValuation_top_iff (x : WittVector p k) :
    wittIntegerValuation p k x = ⊤ ↔ x = 0 := by
  change naturalToRationalTop (IsDiscreteValuationRing.addVal (WittVector p k) x) = ⊤ ↔ _
  rw [naturalToRationalTop_eq_top, IsDiscreteValuationRing.addVal_eq_top_iff]

theorem wittIntegerValuation_p : wittIntegerValuation p k (p : WittVector p k) = 1 := by
  change naturalToRationalTop (IsDiscreteValuationRing.addVal (WittVector p k) (p : WittVector p k)) = 1
  rw [IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p)]
  rfl

theorem wittValuation_denominators : nonZeroDivisors (WittVector p k) ≤
    (AddValuation.toValuation (wittIntegerValuation p k)).supp.primeCompl := by
  intro x hx
  change wittIntegerValuation p k x ≠ ⊤
  exact (wittIntegerValuation_top_iff p k x).not.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hx)

def coefficientValuation : AddValuation (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) (WithTop ℚ) :=
  AddValuation.ofValuation
    ((AddValuation.toValuation (wittIntegerValuation p k)).extendToLocalization
      (wittValuation_denominators p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)))

theorem coefficientValuation_integer (x : WittVector p k) :
    coefficientValuation p k (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x) =
      wittIntegerValuation p k x :=
  congrArg (fun z : Multiplicative (WithTop ℚ)ᵒᵈ => OrderDual.ofDual (Multiplicative.toAdd z))
    ((AddValuation.toValuation (wittIntegerValuation p k)).extendToLocalization_apply_map_apply
      (wittValuation_denominators p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x)

theorem coefficientValuation_p : coefficientValuation p k (p : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) = 1 := by
  rw [← map_natCast (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k))),
    coefficientValuation_integer, wittIntegerValuation_p]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [Module.Finite ℚ_[p] K]

def k0Valuation : AddValuation (MaximalUnramified.K0 p K) (WithTop ℚ) :=
  (coefficientValuation p (FiniteFieldResidue.FieldResidue p K)).comap (k0ModelEquiv p K).symm.toRingHom

theorem k0Valuation_p : k0Valuation p K (p : MaximalUnramified.K0 p K) = 1 := by
  change coefficientValuation p (FiniteFieldResidue.FieldResidue p K) ((k0ModelEquiv p K).symm (p : MaximalUnramified.K0 p K)) = 1
  rw [map_natCast, coefficientValuation_p]

end NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure

namespace NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure.Frobenius

/-! The normalized valuation of the actual unramified field is Frobenius invariant. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified
variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [Fintype k] [CharP k p]

theorem wittIntegerValuation_frobenius (x : WittVector p k) :
    wittIntegerValuation p k (WittVector.frobenius x) = wittIntegerValuation p k x := by
  change naturalToRationalTop (IsDiscreteValuationRing.addVal (WittVector p k) (WittVector.frobenius x)) =
    naturalToRationalTop (IsDiscreteValuationRing.addVal (WittVector p k) x)
  apply congrArg naturalToRationalTop
  by_cases hx : x = 0
  · rw [hx, map_zero]
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' x hx
  have hu0 := IsDiscreteValuationRing.addVal_eq_zero_of_unit u
  have hu1 := IsDiscreteValuationRing.addVal_eq_zero_of_unit
    (Units.map (WittVector.frobenius : WittVector p k →+* WittVector p k).toMonoidHom u)
  change IsDiscreteValuationRing.addVal (WittVector p k) (WittVector.frobenius (u : WittVector p k)) = 0 at hu1
  rw [hu, map_mul, map_pow, map_natCast, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_mul, hu0, hu1]

theorem coefficientValuation_frobenius (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    coefficientValuation p k (UnramifiedCoefficients.coefficientFrobenius (p := p) x) = coefficientValuation p k x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (WittVector p k) x
  rw [map_div₀, UnramifiedCoefficients.coefficientFrobenius_integer, UnramifiedCoefficients.coefficientFrobenius_integer,
    AddValuation.map_div, AddValuation.map_div, coefficientValuation_integer,
    coefficientValuation_integer, coefficientValuation_integer, coefficientValuation_integer,
    wittIntegerValuation_frobenius, wittIntegerValuation_frobenius]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [Module.Finite ℚ_[p] K]

theorem k0Valuation_frobenius (a : MaximalUnramified.K0 p K) :
    k0Valuation p K (k0Frobenius p K a) = k0Valuation p K a := by
  change coefficientValuation p (FiniteFieldResidue.FieldResidue p K)
    ((k0ModelEquiv p K).symm (k0Frobenius p K a)) = _
  rw [k0Frobenius_model_symm, coefficientValuation_frobenius]
  rfl

end NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure.Frobenius

end

end OAI
