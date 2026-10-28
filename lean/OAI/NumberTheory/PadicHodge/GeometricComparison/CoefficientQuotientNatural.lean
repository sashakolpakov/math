import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientOf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition

/-! # Coefficient Quotient Natural -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientNatural.CoefficientQuotientLiftTransition

noncomputable section

/-! Canonical quotient cochain lifts commute with coefficient-ideal transitions. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
  {K L M : CochainComplex (ModuleCat.{v} R) ℕ} (a : K ⟶ L) (b : K ⟶ M) (g : L ⟶ M)
  (ha : ∀ i, (I • ⊤ : Submodule R (K.X i)) ≤ LinearMap.ker (a.f i).hom)
  (hb : ∀ i, (J • ⊤ : Submodule R (K.X i)) ≤ LinearMap.ker (b.f i).hom)
  (h : a ≫ g = b)

include h in
theorem natural : CoefficientQuotientOf.CoefficientQuotientLift.map R I a ha ≫ g =
    IntegralComparison.Module.IdealQuotientTransition.complexMap R I J hIJ K ≫ CoefficientQuotientOf.CoefficientQuotientLift.map R J b hb := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R (K.X i)).mkQ_surjective x
  exact congrArg (fun q : K.X i ⟶ M.X i => q x) (congrArg (fun q => q.f i) h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientNatural.CoefficientQuotientLiftTransition
