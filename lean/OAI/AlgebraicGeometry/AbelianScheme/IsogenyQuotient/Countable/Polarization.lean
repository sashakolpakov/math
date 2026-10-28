import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Positive
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedKernelType

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable

noncomputable section

/-! A geometric polarized abelian variety has a countable model of
its full native polarization: actual dual data, positive isogeny,
finite-flat degree, and every geometric elementary-divisor group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Positive.Construction.CountablePositiveIsogenyModel.kernelType
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    {A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))}
    (M : Positive.Construction.CountablePositiveIsogenyModel A) : M.isogeny.HasPolarizationType δ :=
  AlgebraicallyClosedKernelType.Construction.isogeny_type_of_algebraicallyClosed_field_pullback M.isogeny
    (Spec.map (CommRingCat.ofHom M.model.field.subtype))
    (AbelianModuli.ReferenceFamily.IsogenyComparisonKernel.isogeny_type_of_comparison A.polarization.isogeny
      (M.isogeny.pullback (Spec.map (CommRingCat.ofHom M.model.field.subtype)))
      M.model.sourceRecovery M.model.dualRecovery M.comparison A.polarization.kernelType)

def Positive.Construction.CountablePositiveIsogenyModel.polarization
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    {A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))}
    (M : Positive.Construction.CountablePositiveIsogenyModel A) : AbelianModuli.HilbertConstruction.PolarizationData.Polarization M.model.dual δ :=
  ⟨M.isogeny, M.kernelType, M.positive⟩

theorem Polarization.Construction.countable_full_polarization_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    ∃ M : DualModel.Construction.CountableDualModel A.abelian A.dual, ∃ p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization M.dual δ,
      M.sourceRecovery.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom M.field.subtype))).map p.isogeny.hom =
          A.polarization.isogeny.hom ≫ M.dualRecovery.hom := by
  obtain ⟨M⟩ := Positive.Construction.countable_positive_isogeny_model_exists A
  exact ⟨M.model, M.polarization, M.comparison⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable
