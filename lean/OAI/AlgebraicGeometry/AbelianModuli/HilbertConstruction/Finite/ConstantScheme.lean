import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme

/-! # Constant Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

noncomputable section

/-! Finiteness of constant schemes with finite labels over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {I : Type u}

@[simp]
theorem constantScheme_hom_ι_apply (i : I) (x : S) :
    (ConstantScheme.Iff.constantScheme S I).hom (Sigma.ι (fun _ : I => S) i x) = x :=
  congrArg (fun f : S ⟶ S => f x) (ConstantScheme.Iff.constantScheme_ι_hom i)

/-- A finite disjoint union of identity maps is topologically closed. -/
theorem constantScheme_isClosedMap [Finite I] : IsClosedMap (ConstantScheme.Iff.constantScheme S I).hom := by
  intro C hC
  have heq : (ConstantScheme.Iff.constantScheme S I).hom '' C =
      ⋃ i : I, (Sigma.ι (fun _ : I => S) i) ⁻¹' C := by
    ext s
    constructor
    · rintro ⟨x, hx, hs⟩
      obtain ⟨⟨i, t⟩, rfl⟩ := (sigmaMk (fun _ : I => S)).surjective x
      rw [sigmaMk_mk, constantScheme_hom_ι_apply] at hs
      subst t
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      change Sigma.ι (fun _ : I => S) i s ∈ C
      rw [sigmaMk_mk] at hx
      exact hx
    · intro hs
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
      exact ⟨Sigma.ι (fun _ : I => S) i s, hi, constantScheme_hom_ι_apply i s⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun i => hC.preimage (Sigma.ι (fun _ : I => S) i).continuous)

/-- Finite constant schemes are affine over their base, even when the base is not affine. -/
instance constantScheme_affineHom [Finite I] : IsAffineHom (ConstantScheme.Iff.constantScheme S I).hom := by
  constructor
  intro U hU
  have : IsAffine U.toScheme := hU
  have : IsAffine (ConstantScheme.Iff.constantScheme U.toScheme I).left :=
    inferInstanceAs (IsAffine (∐ fun _ : I => U.toScheme))
  let e : (ConstantScheme.Iff.constantScheme U.toScheme I).left ≅
      ((ConstantScheme.Iff.constantScheme S I).hom ⁻¹ᵁ U).toScheme :=
    ((Over.forget U.toScheme).mapIso (Constant.BaseChange.constantSchemeBaseChangeIso U.ι I)) ≪≫
      pullbackRestrictIsoRestrict (ConstantScheme.Iff.constantScheme S I).hom U
  exact IsAffine.of_isIso e.inv

/-- Finite constant schemes remain topologically closed after every base change. -/
instance constantScheme_universallyClosed [Finite I] :
    UniversallyClosed (ConstantScheme.Iff.constantScheme S I).hom where
  universally_isClosedMap {X Y} i₁ i₂ f h := by
    let e := Constant.BaseChange.constantSchemeBaseChangeIso i₂ I
    have hsnd : IsClosedMap (pullback.snd (ConstantScheme.Iff.constantScheme S I).hom i₂) := by
      have he : e.inv.left ≫ (ConstantScheme.Iff.constantScheme Y I).hom =
          pullback.snd (ConstantScheme.Iff.constantScheme S I).hom i₂ := e.inv.w
      exact he ▸ (constantScheme_isClosedMap (S := Y) (I := I)).comp
        (((Over.forget Y).mapIso e).inv.homeomorph.isClosedMap)
    have he : h.flip.isoPullback.hom ≫ pullback.snd (ConstantScheme.Iff.constantScheme S I).hom i₂ = f :=
      h.flip.isoPullback_hom_snd
    exact he ▸ hsnd.comp h.flip.isoPullback.hom.homeomorph.isClosedMap

/-- A constant scheme with finitely many labels is proper over the base. -/
instance constantScheme_proper [Finite I] : IsProper (ConstantScheme.Iff.constantScheme S I).hom where

/-- A constant scheme with finitely many labels is finite over the base. -/
instance constantScheme_finite [Finite I] : IsFinite (ConstantScheme.Iff.constantScheme S I).hom :=
  IsFinite.of_isProper_of_locallyQuasiFinite _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
