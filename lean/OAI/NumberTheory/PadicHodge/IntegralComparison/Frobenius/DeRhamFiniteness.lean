import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.DifferentialFormFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.HomologyFiniteness

/-! # De Rham Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamFiniteness

noncomputable section

/-!
# IntegralComparison: actual finite-type de Rham homology is finite for its Frobenius coordinate action
-/

open _root_.CategoryTheory

universe u

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C] [Algebra.FiniteType k C]

theorem forms_finite (n : ℕ) : Module.Finite C (DeRhamComplex.forms k C n) := by
  let : Module.Finite C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n) := DifferentialFormFiniteness.forms_finite k C n
  exact IntegralComparison.Finite.ScalarRestriction.finite (FiniteField.frobeniusAlgHom k C).toRingHom
    (IntegralComparison.Finite.FieldFrobenius.finite k C) (ModuleCat.of C (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n))

theorem homology_finite (n : ℕ) : Module.Finite C ((DeRhamComplex.complex k C).homology n) := by
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  let : Module.Finite C ((DeRhamComplex.complex k C).X n) := forms_finite k C n
  exact Independent.HomologyFiniteness.homology_finite (DeRhamComplex.complex k C) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamFiniteness
