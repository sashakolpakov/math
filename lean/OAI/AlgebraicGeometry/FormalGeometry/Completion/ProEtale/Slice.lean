import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.Local
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProEtaleRepresentation

/-! # Slice -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Slice.Construction

noncomputable section

/-!
# Completion: objects over a covering scheme in the actual slice site

Weakly étale schemes over a covering object embed fully faithfully in the
slice of the original pro-étale site. This identifies the actual finite
constant representatives on both sides.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.ProEt)

/-- A weakly étale scheme over the covering object is an object of the original slice site. -/
def proEtaleToSlice : U.left.ProEt ⥤ Over U where
  obj V :=
    let W : X.ProEt := Scheme.ProEt.mk (V.hom ≫ U.hom)
    Over.mk (MorphismProperty.Over.homMk (A := W) (B := U) V.hom rfl)
  map f := Over.homMk (MorphismProperty.Over.homMk f.left (by
    change f.left ≫ _ ≫ U.hom = _ ≫ U.hom
    rw [← Category.assoc, MorphismProperty.Over.w])) (by
      apply MorphismProperty.Over.Hom.ext
      exact MorphismProperty.Over.w f)

/-- Scheme morphisms in this actual slice are exactly morphisms over the covering scheme. -/
def proEtaleToSliceFullyFaithful : (proEtaleToSlice U).FullyFaithful where
  preimage {A B} f := MorphismProperty.Over.homMk f.left.left (by
    exact congrArg (fun g : ((proEtaleToSlice U).obj A).left ⟶ U => g.left) f.w)
  map_preimage f := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl
  preimage_map f := by
    apply MorphismProperty.Over.Hom.ext
    rfl

theorem proEtaleToSlice_finiteCoefficient (ℓ n : ℕ) :
    (proEtaleToSlice U).obj (Finite.ConstantScheme.Construction.finiteCoefficientProEt ℓ n U.left) =
      FiniteTorsor.Local.Construction.finiteCoefficientSlice ℓ n U := rfl

/-- The coefficient algebra is the actual coordinate algebra of the finite coefficient scheme. -/
def finiteCoefficientAlgebra (ℓ n : ℕ) [NeZero (ℓ ^ n)]
    (S : Type u) [CommRing S] : Algebras.Construction.ProEtaleAlgebra S := by
  let V := Finite.ConstantScheme.Construction.finiteCoefficientProEt ℓ n (Spec (CommRingCat.of S))
  have : IsAffine V.left :=
    inferInstanceAs (IsAffine (∐ fun _ : ULift.{u} (ZMod (ℓ ^ n)) => Spec (CommRingCat.of S)))
  exact Affine.ProEtaleRepresentation.Construction.proEtaleAlgebraOfAffine V

/-- Its spectrum is isomorphic to the actual finite coefficient scheme. -/
def finiteCoefficientAlgebraSpecIso (ℓ n : ℕ) [NeZero (ℓ ^ n)]
    (S : Type u) [CommRing S] :
    (Algebras.Construction.proEtaleAlgebraSpec S).obj (op (finiteCoefficientAlgebra ℓ n S)) ≅
      Finite.ConstantScheme.Construction.finiteCoefficientProEt ℓ n (Spec (CommRingCat.of S)) := by
  let V := Finite.ConstantScheme.Construction.finiteCoefficientProEt ℓ n (Spec (CommRingCat.of S))
  have : IsAffine V.left :=
    inferInstanceAs (IsAffine (∐ fun _ : ULift.{u} (ZMod (ℓ ^ n)) => Spec (CommRingCat.of S)))
  exact Affine.ProEtaleRepresentation.Construction.proEtaleAlgebraOfAffineIso V

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Slice.Construction
