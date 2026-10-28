import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalCochainExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition

/-! # Cochain Quotient Transition Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientTransitionCoordinates.PrincipalCochainQuotientTransitionCoordinates

noncomputable section

/-! Original principal-power cochain transitions are the canonical
coefficient-ideal quotient transitions on the same complex. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)
  (n m : ℕ) (hnm : n ≤ m)

theorem transition : PrincipalCochainExact.PrincipalCochainQuotient.transition R C r n m hnm =
    IntegralComparison.Module.IdealQuotientTransition.complexMap R ((Ideal.span {r}) ^ m) ((Ideal.span {r}) ^ n)
      (Ideal.pow_le_pow_right hnm) C := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (((Ideal.span {r}) ^ m) • (⊤ : Submodule R (C.X i))).mkQ_surjective x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientTransitionCoordinates.PrincipalCochainQuotientTransitionCoordinates
