import OAI.NumberTheory.PadicHodge.GeometricComparison.WeaklyEtale
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius

/-! # Prime Power Frobenius Identification -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerFrobeniusIdentification.FiniteFieldFrobeniusGeometry

noncomputable section

/-! At the prime field, Completion's original power morphism is the absolute Frobenius used for the weakly étale base-change theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (κ : ZMod p →+* Γ(X, ⊤))

include κ in
theorem prime_eq_zero : (p : Γ(X, ⊤)) = 0 := by
  rw [← map_natCast κ, ZMod.natCast_self, map_zero]

theorem qPower_eq_absolute :
    AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius (ZMod p) X κ =
      AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out X (prime_eq_zero p X κ) := by
  apply Scheme.Hom.ext (by rfl)
  intro U
  change (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius (ZMod p) X κ).app U ≫
      X.presheaf.map (𝟙 (op U)) =
    (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out X (prime_eq_zero p X κ)).app U
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  ext s
  change s ^ Fintype.card (ZMod p) = s ^ p
  rw [ZMod.card]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerFrobeniusIdentification.FiniteFieldFrobeniusGeometry
