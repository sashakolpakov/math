import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Zero Dimensional Flat -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ZeroDimensionalFlat.Construction

noncomputable section

/-! # Completion: flatness over reduced zero-dimensional rings and affine schemes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Every ring map out of a reduced zero-dimensional ring is flat. -/
theorem ringHom_flat_of_reduced_zeroDimensional {R S : Type u} [CommRing R] [CommRing S]
    [IsReduced R] [Ring.KrullDimLE 0 R] (f : R →+* S) : f.Flat := by
  apply RingHom.Flat.ofLocalizationPrime
  intro P hP
  have : Ring.KrullDimLE 0 (Localization.AtPrime (P.comap f)) :=
    Ring.KrullDimLE.of_isLocalization (P.comap f)
      (Ideal.mem_minimalPrimes_of_krullDimLE_zero (P.comap f)) _
  exact RingHom.Flat.of_isField Ring.KrullDimLE.isField_of_isReduced _

/-- Every morphism into a reduced zero-dimensional affine scheme is flat. -/
theorem schemeMap_flat_of_reduced_zeroDimensional_affine {X Y : Scheme.{u}}
    [IsAffine Y] [IsReduced Γ(Y, ⊤)] [Ring.KrullDimLE 0 Γ(Y, ⊤)] (f : X ⟶ Y) :
    Flat f := by
  refine (MorphismProperty.cancel_right_of_respectsIso @Flat _ Y.isoSpec.hom).mp ?_
  refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i => ?_
  rw [← Spec.map_preimage (X.affineCover.f i ≫ f ≫ Y.isoSpec.hom),
    HasRingHomProperty.Spec_iff (P := @Flat)]
  exact ringHom_flat_of_reduced_zeroDimensional _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ZeroDimensionalFlat.Construction
