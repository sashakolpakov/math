import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Polarization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedLevelDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizedLevelRecovery

/-! # Polarized Level Model -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PolarizedLevelModel.Construction

noncomputable section

/-! Full polarized abelian objects, including their specified ordered
level, descend to a countable algebraically closed subfield. The
recovery is an isomorphism in the original HilbertConstruction moduli problem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizedLevelRecovery

structure CountablePolarizedLevelModel {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) where
  field : Subfield k
  [countable : Countable field]
  [algebraicallyClosed : IsAlgClosed field]
  polarized : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of field))
  recovery : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A (polarized.pullback (Spec.map (CommRingCat.ofHom field.subtype)))

attribute [instance] CountablePolarizedLevelModel.countable CountablePolarizedLevelModel.algebraicallyClosed

set_option backward.isDefEq.respectTransparency false in
theorem countable_polarized_full_level_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    Nonempty (CountablePolarizedLevelModel A) := by
  obtain ⟨M, p, hp⟩ := Polarization.Construction.countable_full_polarization_model_exists A
  let u := Spec.map (CommRingCat.ofHom M.field.subtype)
  obtain ⟨α, hα⟩ := AlgebraicallyClosedLevelDescent.Construction.algebraicallyClosed_fullLevel_descends M.abelian u
    (A.level.transport M.sourceRecovery)
  let B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of M.field)) :=
    ⟨M.abelian, M.dual, p, α⟩
  exact ⟨{
    field := M.field
    polarized := B
    recovery := AbelianModuli.ReferenceFamily.CartesianPolarizedLevelRecovery.levelIso_of_cartesian_recovery A B u M.sourceRecovery M.dualRecovery hp M.poincare hα }⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PolarizedLevelModel.Construction
