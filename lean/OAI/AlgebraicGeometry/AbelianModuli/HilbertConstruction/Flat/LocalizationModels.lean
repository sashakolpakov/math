import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorIsoDescent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Smooth.Basic

/-! # Localization Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LocalizationModels

noncomputable section

/-! Principal-open localizations of flat finite type models retain both properties. -/

open TensorProduct

universe u

variable {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]

theorem localizationAway_flat_overBase [Module.Flat C A] (a : A) :
    Module.Flat C (Localization.Away a) := Module.Flat.trans C A (Localization.Away a)

theorem localizationAway_finiteType_overBase [Algebra.FiniteType C A] (a : A) :
    Algebra.FiniteType C (Localization.Away a) := by
  have : Algebra.FinitePresentation A (Localization.Away a) := IsLocalization.Away.finitePresentation a
  exact Algebra.FiniteType.trans (S := A) (inferInstanceAs (Algebra.FiniteType C A))
    (inferInstanceAs (Algebra.FiniteType A (Localization.Away a)))

def principalModelBaseChangeIso (R : Type u) [CommRing R] [Algebra C R] (a : A) :
    R ⊗[C] Localization.Away a ≃ₐ[R] Localization.Away ((1 : R) ⊗ₜ[C] a) :=
  IsLocalization.Away.tensorProductEquivTMulRight C R a (Localization.Away a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LocalizationModels
