import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapControlledIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelSums

/-! # Sums -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Sums.Construction

noncomputable section

/-! Controlled transforms of native sums at a common permissible control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_mul_iSup {X : Scheme} {ι : Type*}
    (K : X.IdealSheafData) (J : ι → X.IdealSheafData) :
    K * (⨆ i, J i) = ⨆ i, K * J i := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [Ideal.mul_iSup]

theorem globalBlowupControlledIdeal_iSup {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] {ι : Type*}
    (I : X.IdealSheafData) (J : ι → X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (hp : ∀ i, J i ≤ I ^ b) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (⨆ i, J i) hI b =
      ⨆ i, GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (J i) hI b := by
  apply Locally.PrincipalIdealCancellation.Construction.locallyPrincipal_idealSheaf_mul_left_injective
    ((I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b)
    (Integral.IdealSheafProducts.Construction.idealSheaf_pow_ne_bot _ (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I I hI hI) b)
    ((Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal I hI).pow b)
  change (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b *
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (⨆ i, J i) hI b =
    (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b * (⨆ i, GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (J i) hI b)
  rw [Factorization.Construction.globalBlowup_controlledIdeal_factorization I _ hI b (iSup_le hp),
    Affine.KernelSums.Construction.idealSheaf_comap_iSup, idealSheaf_mul_iSup]
  exact congrArg iSup (funext fun i =>
    (Factorization.Construction.globalBlowup_controlledIdeal_factorization I (J i) hI b (hp i)).symm)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Sums.Construction
