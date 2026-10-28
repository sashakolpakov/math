import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineProduct
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LaurentNaturality

/-! # Affine Character Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterValues.Construction

noncomputable section

/-!
# CartierDuality: coordinate values of affine character-sheaf sections
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [HopfAlgebra R A]

/-- The native pullback character associated with an affine-coordinate
character is given by the canonical source and target comparisons. -/
theorem affineGroupCharacterSectionsEquiv_native
    (h : Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A) ⟶ Characters.Construction.multiplicativeGroupScheme S) :
    SliceCharacters.Construction.Schemes.characterSheaf_sectionsPullbackEquiv (Spec (CommRingCat.of R))
      (Characters.Construction.affineHopfGroupScheme R A)
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
      (AffinePullback.Construction.affineGroupCharacterSectionsEquiv R S A h) =
    (((AffinePullback.Construction.affineHopfPullbackIso R S A).hom ≫ h) ≫
      (AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso S).inv) ≫
      (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).inv := by
  let e := SliceCharacters.Construction.Schemes.characterSheaf_sectionsPullbackEquiv (Spec (CommRingCat.of R))
    (Characters.Construction.affineHopfGroupScheme R A)
    ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
  change e (e.symm ((((AffinePullback.Construction.affineHopfPullbackIso R S A).hom ≫ h) ≫
    (AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso S).inv) ≫
      (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).inv)) = _
  exact e.apply_symm_apply _

/-- The test-scheme character of an affine section uses the canonical
coordinate comparisons on source and target. -/
theorem affineGroupCharacterSectionsEquiv_test
    (h : Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A) ⟶ Characters.Construction.multiplicativeGroupScheme S) :
    SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv (Spec (CommRingCat.of R))
      (Characters.Construction.affineHopfGroupScheme R A)
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
      (AffinePullback.Construction.affineGroupCharacterSectionsEquiv R S A h) =
    ((AffinePullback.Construction.affineHopfPullbackIso R S A).hom ≫ h) ≫
      (AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso S).inv := by
  let e := SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv (Spec (CommRingCat.of R))
    (Characters.Construction.affineHopfGroupScheme R A)
    ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
  change e (e.symm (((AffinePullback.Construction.affineHopfPullbackIso R S A).hom ≫ h) ≫
    (AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso S).inv)) = _
  exact e.apply_symm_apply _

/-- After projection to the integral multiplicative group, evaluation
of an affine character section is exactly its coordinate character map. -/
theorem affineGroupCharacterSectionsEquiv_value
    (h : Characters.Construction.affineHopfGroupScheme S (S ⊗[R] A) ⟶ Characters.Construction.multiplicativeGroupScheme S) :
    (SliceCharacters.Construction.Schemes.characterValue (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
      (AffinePullback.Construction.affineGroupCharacterSectionsEquiv R S A h)).left ≫
        SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral (Spec (CommRingCat.of R)) =
    ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso (Spec (CommRingCat.of R))
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))).hom.app
        (Characters.Construction.affineHopfGroupScheme R A).X).left ≫
      (AffinePullback.Construction.affineHopfPullbackIso R S A).hom.hom.hom.left ≫ h.hom.hom.left ≫
        Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapRingHom (Multiplicative ℤ)
          ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom))) := by
  let X := Spec (CommRingCat.of R)
  let G := Characters.Construction.affineHopfGroupScheme R A
  let T := (Spec (CommRingCat.of S)).asOver X
  let χ := AffinePullback.Construction.affineGroupCharacterSectionsEquiv R S A h
  let p := ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso X T).hom.app G.X).left
  let a := AffinePullback.Construction.affineHopfPullbackIso R S A
  let m := AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso S
  have hvalue := SliceCharacters.Construction.Schemes.characterValue_integral X G T χ
  have hchar := congrArg
    (fun f : (Over.pullback T.hom).mapGrp.obj G ⟶
        CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left => f.hom.hom.left)
    (affineGroupCharacterSectionsEquiv_test R S A h)
  change (SliceCharacters.Construction.Schemes.characterSheaf_testCharacterEquiv X G T χ).hom.hom.left =
    (a.hom.hom.hom.left ≫ h.hom.hom.left) ≫ m.inv.hom.hom.left at hchar
  have hmiddle := congrArg (fun f => p ≫ f ≫
    SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral T.left) hchar
  simp only [Category.assoc] at hmiddle
  have hfinal := congrArg (fun f => p ≫ a.hom.hom.hom.left ≫ h.hom.hom.left ≫ f)
    (AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso_inv_integralProjection S)
  exact hvalue.trans (hmiddle.trans hfinal)

/-- Integral values determine character sections on every test scheme. -/
theorem Schemes.characterValue_integral_ext
    (X : Scheme.{u}) (G : Grp (Over X)) (T : Over X)
    {χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf X G).obj.obj (Opposite.op T)}
    (h : (SliceCharacters.Construction.Schemes.characterValue X G T χ).left ≫ SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral X =
      (SliceCharacters.Construction.Schemes.characterValue X G T ψ).left ≫ SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral X) :
    χ = ψ := by
  apply SliceCharacters.Construction.Slices.sliceNatTrans_ext T G (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver X)
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact h
  · exact (SliceCharacters.Construction.Schemes.characterValue X G T χ).w.trans
      (SliceCharacters.Construction.Schemes.characterValue X G T ψ).w.symm

/-- The sheaf section attached to a group-like element of the
base-changed coordinate algebra. -/
def affineGroupLikeSection (z : GroupLike S (S ⊗[R] A)) :
    (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.obj
      (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))) :=
  AffinePullback.Construction.affineGroupCharacterSectionsEquiv R S A (Characters.Construction.groupLikeEquivSchemeCharacters S (S ⊗[R] A) z)

/-- Evaluating an affine section and projecting to the integral
multiplicative group gives exactly its integral Laurent-coordinate map. -/
theorem affineGroupLikeSection_integralValue (z : GroupLike S (S ⊗[R] A)) :
    (SliceCharacters.Construction.Schemes.characterValue (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
      (affineGroupLikeSection R S A z)).left ≫
        SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral (Spec (CommRingCat.of R)) =
    AffineProduct.Construction.affineProductCoordinates R S A ≫
      Spec.map (CommRingCat.ofHom (LaurentNaturality.Construction.integralCharacterMap S (S ⊗[R] A) z)) := by
  let c := (Characters.Construction.groupLikeEquivSchemeCharacters S (S ⊗[R] A) z).hom.hom.left
  let d := Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapRingHom (Multiplicative ℤ)
    ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom)))
  have hcd : c ≫ d = Spec.map (CommRingCat.ofHom (LaurentNaturality.Construction.integralCharacterMap S (S ⊗[R] A) z)) := by
    change Spec.map (CommRingCat.ofHom
        (Characters.Construction.groupLikeEquivHopfCharacters S (S ⊗[R] A) z).toAlgHom.toRingHom) ≫ d = _
    unfold LaurentNaturality.Construction.integralCharacterMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hcomp {X₁ X₂ X₃ X₄ X₅ : Scheme.{u}}
      (p : X₁ ⟶ X₂) (a : X₂ ⟶ X₃) (c : X₃ ⟶ X₄) (d : X₄ ⟶ X₅)
      (q : X₁ ⟶ X₃) (r : X₃ ⟶ X₅) (hp : p ≫ a = q) (hc : c ≫ d = r) :
      p ≫ a ≫ c ≫ d = q ≫ r := by
    rw [hc, ← Category.assoc, hp]
  exact (affineGroupCharacterSectionsEquiv_value R S A
    (Characters.Construction.groupLikeEquivSchemeCharacters S (S ⊗[R] A) z)).trans
      (hcomp _ _ c d _ _ (AffineProduct.Construction.affineCharacterProductComparison R S A) hcd)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterValues.Construction
