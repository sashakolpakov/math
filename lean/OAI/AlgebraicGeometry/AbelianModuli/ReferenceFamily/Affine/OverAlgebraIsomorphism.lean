import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Over Algebra Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverAlgebraIsomorphism

noncomputable section

section

/-! Actual isomorphisms of affine schemes over a base spectrum give
algebra isomorphisms over that same base, with their scheme map retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

def affineOverIsoAlgebraEquiv (e : EtaleSplittingAt.EtaleSplitting.affineOver R A ≅ EtaleSplittingAt.EtaleSplitting.affineOver R B) : B ≃ₐ[R] A :=
  CommAlgCat.algEquivOfIso
    (((algSpec.fullyFaithful (R := CommRingCat.of R)).preimageIso
      (X := Opposite.op (CommAlgCat.of R A)) (Y := Opposite.op (CommAlgCat.of R B)) e).unop)

theorem affineOverIsoAlgebraEquiv_spec (e : EtaleSplittingAt.EtaleSplitting.affineOver R A ≅ EtaleSplittingAt.EtaleSplitting.affineOver R B) :
    Spec.map (CommRingCat.ofHom (affineOverIsoAlgebraEquiv R A B e).toRingHom) = e.hom.left := by
  change ((algSpec (CommRingCat.of R)).map
    ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
      (X := Opposite.op (CommAlgCat.of R A)) (Y := Opposite.op (CommAlgCat.of R B)) e.hom)).left = _
  exact congrArg Over.Hom.left ((algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage
    (X := Opposite.op (CommAlgCat.of R A)) (Y := Opposite.op (CommAlgCat.of R B)) e.hom)

end

section

/-! Reconstructing affine algebra isomorphisms is faithful and reverses
composition, with the literal scheme maps as witnesses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem affineOverIsoAlgebraEquiv_injective :
    Function.Injective (affineOverIsoAlgebraEquiv R A B) := by
  intro e f h
  apply Iso.ext
  apply Over.OverMorphism.ext
  have hs := congrArg (fun a : B ≃ₐ[R] A => Spec.map (CommRingCat.ofHom a.toRingHom)) h
  simpa only [affineOverIsoAlgebraEquiv_spec] using hs

theorem affineOverIsoAlgebraEquiv_refl :
    affineOverIsoAlgebraEquiv R A A (Iso.refl (EtaleSplittingAt.EtaleSplitting.affineOver R A)) = AlgEquiv.refl := by
  have hs : Spec.map (CommRingCat.ofHom
      (affineOverIsoAlgebraEquiv R A A (Iso.refl (EtaleSplittingAt.EtaleSplitting.affineOver R A))).toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgEquiv.refl (R := R) (A₁ := A)).toRingHom) := by
    rw [affineOverIsoAlgebraEquiv_spec]
    exact (Spec.map_id (CommRingCat.of A)).symm
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact AlgEquiv.ext (fun a => RingHom.congr_fun hr a)

variable (C : Type) [CommRing C] [Algebra R C]

theorem affineOverIsoAlgebraEquiv_trans (e : EtaleSplittingAt.EtaleSplitting.affineOver R A ≅ EtaleSplittingAt.EtaleSplitting.affineOver R B)
    (f : EtaleSplittingAt.EtaleSplitting.affineOver R B ≅ EtaleSplittingAt.EtaleSplitting.affineOver R C) :
    affineOverIsoAlgebraEquiv R A C (e ≪≫ f) =
      (affineOverIsoAlgebraEquiv R B C f).trans (affineOverIsoAlgebraEquiv R A B e) := by
  have hs : Spec.map (CommRingCat.ofHom (affineOverIsoAlgebraEquiv R A C (e ≪≫ f)).toRingHom) =
      Spec.map (CommRingCat.ofHom
        ((affineOverIsoAlgebraEquiv R B C f).trans (affineOverIsoAlgebraEquiv R A B e)).toRingHom) := by
    rw [affineOverIsoAlgebraEquiv_spec]
    change e.hom.left ≫ f.hom.left = Spec.map
      (CommRingCat.ofHom (affineOverIsoAlgebraEquiv R B C f).toRingHom ≫
        CommRingCat.ofHom (affineOverIsoAlgebraEquiv R A B e).toRingHom)
    simp only [Spec.map_comp, affineOverIsoAlgebraEquiv_spec]
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact AlgEquiv.ext (fun a => RingHom.congr_fun hr a)

end

/-! Reconstructing the algebra from its induced affine scheme
isomorphism returns the original algebra isomorphism exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem affineOverIsoAlgebraEquiv_affineAlgIso (e : A ≃ₐ[R] B) :
    affineOverIsoAlgebraEquiv R B A (EtaleSplittingAt.EtaleSplitting.affineAlgIso R A e) = e := by
  have hs : Spec.map (CommRingCat.ofHom
      (affineOverIsoAlgebraEquiv R B A (EtaleSplittingAt.EtaleSplitting.affineAlgIso R A e)).toRingHom) =
      Spec.map (CommRingCat.ofHom e.toRingHom) :=
    affineOverIsoAlgebraEquiv_spec R B A (EtaleSplittingAt.EtaleSplitting.affineAlgIso R A e)
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact AlgEquiv.ext (fun a => RingHom.congr_fun hr a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverAlgebraIsomorphism
