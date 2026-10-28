import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

/-! # Coefficient Derivation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.CoefficientDerivationKernel

noncomputable section

/-! Derivations vanishing on the base are precisely relative
derivations. The comparison is linear over the coefficient algebra. -/

variable (k R S C : Type) [CommRing k] [CommRing R] [CommRing S] [CommRing C]
    [Algebra k R] [Algebra k S] [Algebra k C] [Algebra R S] [Algebra R C] [Algebra S C]
    [IsScalarTower k R S] [IsScalarTower k R C] [IsScalarTower k S C] [IsScalarTower R S C]

def relativeCoefficientDerivation (d : Derivation k S C)
    (h : ∀ r : R, d (algebraMap R S r) = 0) : Derivation R S C where
  toLinearMap := {
    toFun := d
    map_add' := d.map_add
    map_smul' := fun r s => by
      rw [Algebra.smul_def, d.leibniz, h r, smul_zero, add_zero]
      exact IsScalarTower.algebraMap_smul S r (d s) }
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz

def relativeCoefficientDerivationKernelEquiv :
    (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).ker ≃ₗ[C] Derivation R S C where
  toFun d := relativeCoefficientDerivation k R S C d.val (fun r => Derivation.congr_fun d.property r)
  invFun d := ⟨d.restrictScalars k, by
    apply Derivation.ext
    intro r
    exact d.map_algebraMap r⟩
  left_inv d := by
    apply Subtype.ext
    apply Derivation.ext
    intro s
    rfl
  right_inv d := by
    apply Derivation.ext
    intro s
    rfl
  map_add' d e := by
    apply Derivation.ext
    intro s
    rfl
  map_smul' a d := by
    apply Derivation.ext
    intro s
    rfl

omit [IsScalarTower k S C] in
theorem relativeCoefficientDerivationKernelEquiv_apply
    (d : (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S C).ker) (s : S) :
    relativeCoefficientDerivationKernelEquiv k R S C d s = d.val s := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.CoefficientDerivationKernel
