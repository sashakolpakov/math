import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.DualLineModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PositiveFormulaDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationFormulaRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PositiveFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GroundFormulaGeometricPositivity
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale

/-! # Positive -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Positive.Construction

noncomputable section

/-! The original positive polarization isogeny has a countable
algebraically closed model with full native dual data and positivity
on every geometric fiber. Kernel type and ordered level are separate
remaining parts of the full PEL field model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

structure CountablePositiveIsogenyModel {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) where
  model : DualModel.Construction.CountableDualModel A.abelian A.dual
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny model.abelian model.dual.abelian
  etale : Etale isogeny.hom.left
  comparison : model.sourceRecovery.hom ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom model.field.subtype))).map isogeny.hom =
      A.polarization.isogeny.hom ≫ model.dualRecovery.hom
  positive : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ Spec (.of model.field)),
      AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber model.dual isogeny.hom K s

set_option backward.isDefEq.respectTransparency false in
theorem countable_positive_isogeny_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    Nonempty (CountablePositiveIsogenyModel A) := by
  obtain ⟨L, hL, _, hformula⟩ := Picard.PoincareBundle.Reference.PositiveFormula.of_polarization A.dual A.polarization
  obtain ⟨M₀⟩ := DualModel.Construction.countable_polarized_dual_model_exists A
  obtain ⟨M⟩ := DualLineModel.Construction.countable_dual_line_model_exists M₀ L
  let F := M.model.field
  let u := Spec.map (CommRingCat.ofHom F.subtype)
  have : Etale A.polarization.isogeny.hom.left :=
    CentralAction.PolarizationEtale.Construction.polarization_etale A.polarization.isogeny δ A.polarization.kernelType
  obtain ⟨p, hp, hc⟩ := RecoveredDescent.Construction.algebraicallyClosed_etale_isogeny_of_recovery F k
    M.model.abelian M.model.dual.abelian A.abelian A.dual.abelian
    M.model.sourceRecovery M.model.dualRecovery A.polarization.isogeny
  let Q := M.model.dual.poincare.pullback (p.hom ⊗ₘ 𝟙 M.model.abelian.scheme).left
  let P := A.dual.poincare.pullback (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme).left
  have hQ := PolarizationFormulaRecovery.Construction.recovered_polarization_biextension_class A.abelian A.dual
    M.model.abelian M.model.dual u M.model.sourceRecovery M.model.dualRecovery
    A.polarization.isogeny.hom p.hom hc M.model.poincare
  have hpos : AbelianModuli.ReferenceFamily.PositiveLineOn.PositiveLineFormula M.model.abelian Q :=
    IsogenyQuotient.Field.PositiveFormulaDescent.Construction.positiveLineFormula_of_recovered_field_witness u M.model.abelian A.abelian
      M.model.sourceRecovery M.line L Q P M.recovery hQ hL (Quotient.sound hformula)
  exact ⟨{
    model := M.model
    isogeny := p
    etale := hp
    comparison := hc
    positive := Picard.PoincareBundle.GroundFormulaGeometricPositivity.positiveOnGeometricFiber M.model.dual p.hom hpos }⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Positive.Construction
