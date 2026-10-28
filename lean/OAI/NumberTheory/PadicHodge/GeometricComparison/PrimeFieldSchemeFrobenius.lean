import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius

/-! # Prime Field Scheme Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeFieldSchemeFrobenius.Crystalline

noncomputable section

/-! The independently constructed absolute and finite-field Frobenius maps coincide over the prime field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem schemeFrobenius_eq_finiteField (q : ℕ) [Fact q.Prime]
    (X : Over (Spec (CommRingCat.of (ZMod q)))) :
    PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius q (ZMod q) X =
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left := by
  apply Scheme.Hom.ext (by rfl)
  intro U
  change (PeriodInvariants.WittFrobeniusGeometry.schemeFrobenius q (ZMod q) X).app U ≫
      X.left.presheaf.map (𝟙 (Opposite.op U)) =
        (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left.app U
  erw [X.left.presheaf.map_id, Category.comp_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change s ^ q = s ^ Fintype.card (ZMod q)
  rw [ZMod.card]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrimeFieldSchemeFrobenius.Crystalline
