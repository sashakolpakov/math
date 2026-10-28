import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Complement
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ImageCongruence

/-! # Order Locus Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation.Construction

noncomputable section

/-! Permissible blowups preserve the whole original open set below the fixed order threshold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

theorem global_tangent_le_permissible_center (J I : X.IdealSheafData) (n : ℕ)
    (hp : J ≤ I ^ (n + 1)) : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≤ I := by
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  exact Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center ℂ (J.ideal U) (I.ideal U) n (hp U)

variable [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowup_preserves_orderComplement (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ∣_ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support.compl) := by
  apply Blowup.Complement.Construction.globalBlowup_isIso_on_open I hI
  have hn : b - 1 + 1 = b := by omega
  have hle := global_tangent_le_permissible_center f J I (b - 1) (hn.symm ▸ hp)
  have hs := Scheme.IdealSheafData.support_antitone hle
  intro x hx
  exact fun hi => hx (hs hi)

theorem globalBlowup_orderComplement_preimage_le (I J : X.IdealSheafData) (hI : I ≠ ⊥)
    (b : ℕ) (hb : 0 < b) (hp : J ≤ I ^ b) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)] :
    GlobalBlowup.Data.Construction.globalBlowupToBase I hI ⁻¹ᵁ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support.compl ≤
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) (b - 1)).support.compl := by
  have hn : 1 + (b - 1) = b := by omega
  have hdiff := DifferentialTransform.Construction.globalBlowup_relativeDifferential_controlled_le f I J hI 1 (b - 1) (hn.symm ▸ hp)
  rw [hn] at hdiff
  have htotal := (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)) 1
    (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).trans hdiff
  have hs := Scheme.IdealSheafData.support_antitone htotal
  rw [Scheme.IdealSheafData.support_comap] at hs
  intro x hx
  exact fun h => hx (hs h)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation.Construction
