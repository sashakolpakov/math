import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Equivalent Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.EquivalentDimensions

noncomputable section

/-! Restriction along a ring isomorphism preserves the dimension of a module. -/
open _root_.CategoryTheory
universe u

theorem restrictScalars_finrank_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (M : ModuleCat.{u} S) :
    Module.finrank R ((ModuleCat.restrictScalars.{u} e.toRingHom).obj M) = Module.finrank S M := by
  have h : Module.rank R ((ModuleCat.restrictScalars.{u} e.toRingHom).obj M) = Module.rank S M :=
    rank_eq_of_equiv_equiv e (AddEquiv.refl M) e.bijective (fun _ _ => rfl)
  exact congrArg Cardinal.toNat h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.EquivalentDimensions
