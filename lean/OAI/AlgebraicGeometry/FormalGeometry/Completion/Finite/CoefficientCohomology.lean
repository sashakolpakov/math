import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Coefficient Cohomology -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction

noncomputable section

/-!
# Completion: degree-one reduction to finite coefficients

This uses the exact sequence of actual coefficient sheaves. Multiplication
by ℓⁿ on integral H¹ is injective, and the kernel of reduction modulo ℓⁿ
consists exactly of ℓⁿ multiples.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})

/-- Reduction of actual integral cohomology to finite coefficients. -/
def integralEllAdicFiniteReduction (d : ℕ) :
    X.EllAdicCohomology ℓ d →+ (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H d :=
  Sheaf.H.map (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X) d

/-- Every degree-zero finite-coefficient class lifts integrally. -/
theorem integralEllAdicFiniteReduction_zero_surjective :
    Function.Surjective (integralEllAdicFiniteReduction ℓ n X 0) := by
  change Function.Surjective (Sheaf.H.map (CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X) 0)
  intro y
  let hT : IsTerminal (⊤_ X.ProEt) := terminalIsTerminal
  obtain ⟨x, hx⟩ := CoefficientSheaf.Construction.finiteEllAdicReduction_app_surjective ℓ n X (op (⊤_ X.ProEt))
    (Sheaf.H.equiv₀ _ hT y)
  refine ⟨(Sheaf.H.equiv₀ (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) hT).symm x, ?_⟩
  apply (Sheaf.H.equiv₀ (CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X) hT).injective
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply, hx]

/-- Integral H¹ has no ℓ-power torsion. -/
theorem integralEllAdicH1_pow_smul_eq_zero (x : X.EllAdicCohomology ℓ 1)
    (hx : (ℓ : ℤ_[ℓ]) ^ n • x = 0) : x = 0 := by
  let S := CoefficientSheaf.Construction.finiteEllAdicShortComplex ℓ n X
  have hS : S.ShortExact := CoefficientSheaf.Construction.finiteEllAdicShortComplex_shortExact ℓ n X
  change (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).H 1 at x
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (ProetalePullback.Construction.proEtIntegerConstant X) hS x hx rfl
  obtain ⟨y, hy⟩ := integralEllAdicFiniteReduction_zero_surjective ℓ n X z
  rw [← hz, ← hy]
  change (y.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass (zero_add 1) = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- The kernel of finite reduction on actual H¹ consists of ℓⁿ multiples. -/
theorem integralEllAdicFiniteReduction_one_eq_zero_iff (x : X.EllAdicCohomology ℓ 1) :
    integralEllAdicFiniteReduction ℓ n X 1 x = 0 ↔
      ∃ y : X.EllAdicCohomology ℓ 1, (ℓ : ℤ_[ℓ]) ^ n • y = x := by
  let S := CoefficientSheaf.Construction.finiteEllAdicShortComplex ℓ n X
  have hS : S.ShortExact := CoefficientSheaf.Construction.finiteEllAdicShortComplex_shortExact ℓ n X
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₂ (ProetalePullback.Construction.proEtIntegerConstant X) hS x hx
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero 1)).comp (Ext.mk₀ S.g) (add_zero 1) = 0
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, S.zero, Ext.mk₀_zero, Ext.comp_zero]

/-- Actual integral H¹ is torsion-free over the integral ℓ-adic coefficient ring. -/
instance integralEllAdicH1_isTorsionFree :
    Module.IsTorsionFree (ℤ_[ℓ]) (X.EllAdicCohomology ℓ 1) := by
  apply Module.isTorsionFree_iff_smul_eq_zero.mpr
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  apply Or.inr
  rw [PadicInt.unitCoeff_spec ha, mul_smul, (PadicInt.unitCoeff ha).isUnit.smul_eq_zero] at hx
  exact integralEllAdicH1_pow_smul_eq_zero ℓ a.valuation X x hx

/-- Integral classes embed into the actual H¹ with algebraic ℓ-adic coefficients. -/
theorem integralEllAdicH1_scalarExtension_injective :
    Function.Injective (TensorProduct.mk (ℤ_[ℓ]) (AlgebraicClosure ℚ_[ℓ])
      (X.EllAdicCohomology ℓ 1) 1) := by
  have : FaithfulSMul (ℤ_[ℓ]) (AlgebraicClosure ℚ_[ℓ]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq (ℤ_[ℓ]) (ℚ_[ℓ]) (AlgebraicClosure ℚ_[ℓ])]
      exact (RingHom.injective (algebraMap (ℚ_[ℓ]) (AlgebraicClosure ℚ_[ℓ]))).comp
        (show Function.Injective (algebraMap (ℤ_[ℓ]) (ℚ_[ℓ])) from Subtype.val_injective))
  exact Module.Flat.tensorProduct_mk_injective _ _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction
