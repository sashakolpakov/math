import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterValues
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent

/-! # Affine Sheaf Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineSheafIso.Construction

noncomputable section

/-!
# CartierDuality: the affine Cartier character-sheaf comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [HopfAlgebra R A]

/-- Restriction of an affine character section agrees with applying the
test-algebra map to its tensor-product coordinate element. -/
theorem affineGroupLikeSection_restrict
    (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
    (z : GroupLike S (S ⊗[R] A)) (w : GroupLike T (T ⊗[R] A))
    (hw : Algebra.TensorProduct.map f (AlgHom.id R A) z.val = w.val) :
    (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.map
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op).op
        (AffineCharacterValues.Construction.affineGroupLikeSection R S A z) = AffineCharacterValues.Construction.affineGroupLikeSection R T A w := by
  let X := Spec (CommRingCat.of R)
  let G := Characters.Construction.affineHopfGroupScheme R A
  let U := (Spec (CommRingCat.of S)).asOver X
  let V := (Spec (CommRingCat.of T)).asOver X
  let p : V ⟶ U := (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op
  let P := (Limits.prod.map p (𝟙 G.X)).left
  let c := AffineProduct.Construction.affineProductCoordinates R S A
  let d := AffineProduct.Construction.affineProductCoordinates R T A
  let a := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R A)).toRingHom)
  let b := Spec.map (CommRingCat.ofHom (LaurentNaturality.Construction.integralCharacterMap S (S ⊗[R] A) z))
  let e := Spec.map (CommRingCat.ofHom (LaurentNaturality.Construction.integralCharacterMap T (T ⊗[R] A) w))
  apply AffineCharacterValues.Construction.Schemes.characterValue_integral_ext X G V
  have hr := congrArg (fun k : V ⨯ G.X ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver X).X =>
    k.left ≫ SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral X)
    (SliceCharacters.Construction.Schemes.characterValue_restrict X G p (AffineCharacterValues.Construction.affineGroupLikeSection R S A z))
  have hz := AffineCharacterValues.Construction.affineGroupLikeSection_integralValue R S A z
  have hw' := AffineCharacterValues.Construction.affineGroupLikeSection_integralValue R T A w
  have hn : P ≫ c = d ≫ a := AffineProduct.Construction.affineProductCoordinates_natural R S A T f
  have hs : a ≫ b = e := by
    have h := congrArg (fun k => Spec.map (CommRingCat.ofHom k))
      (LaurentNaturality.Construction.integralCharacterMap_natural S (S ⊗[R] A) T (T ⊗[R] A) z w
        (Algebra.TensorProduct.map f (AlgHom.id R A)).toRingHom hw)
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at h
    exact h
  have hr' := hr.trans ((Category.assoc P
    (SliceCharacters.Construction.Schemes.characterValue X G U (AffineCharacterValues.Construction.affineGroupLikeSection R S A z)).left
    (SliceCharacters.Construction.Schemes.multiplicativeGroupToIntegral X)).trans (congrArg (fun k => P ≫ k) hz))
  have hc : P ≫ c ≫ b = d ≫ e :=
    (Category.assoc P c b).symm.trans
      ((congrArg (fun k => k ≫ b) hn).trans
        ((Category.assoc d a b).trans (congrArg (fun k => d ≫ k) hs)))
  exact hr'.trans (hc.trans hw'.symm)

variable [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

/-- The universal section uses the group-like coevaluation element. -/
theorem affineCartierUniversalCharacter_eq_groupLikeSection :
    CharacterMap.Construction.affineCartierUniversalCharacter R A =
      AffineCharacterValues.Construction.affineGroupLikeSection R (DualAlgebra.Construction.DualCoordinate R A) A (Naturality.Construction.universalAffineCharacter R A) :=
  rfl

/-- Evaluating the universal character at an algebra point gives the
character defined by the corresponding group-like element. -/
theorem affineCartierCharacterMap_apply_algHom
    (g : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] S) :
    (CharacterMap.Construction.affineCartierCharacterMap R A).app
      (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R))))
        (ULift.up ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op)) =
      AffineCharacterValues.Construction.affineGroupLikeSection R S A (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A g) := by
  let X := Spec (CommRingCat.of R)
  let T := (Spec (CommRingCat.of S)).asOver X
  let D := ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))
  let p : T ⟶ D := (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g).op
  have hu := congrArg
    (fun χ => (CharacterSheaf.Construction.Schemes.characterSheaf X (Characters.Construction.affineHopfGroupScheme R A)).obj.map p.op χ)
    (affineCartierUniversalCharacter_eq_groupLikeSection R A)
  have hbase : Algebra.TensorProduct.map g (AlgHom.id R A)
      (Naturality.Construction.universalAffineCharacter R A).val = (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A g).val :=
    (Naturality.Construction.universalAffineCharacter_baseChange R A g).symm
  have hn := affineGroupLikeSection_restrict R (DualAlgebra.Construction.DualCoordinate R A) A S g
    (Naturality.Construction.universalAffineCharacter R A) (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A g) hbase
  exact (CharacterMap.Construction.affineCartierCharacterMap_apply R A T p).trans (hu.trans hn)

/-- On an affine test scheme, the canonical character-sheaf map is the
proved equivalence between dual points and character sections. -/
theorem affineCartierCharacterMap_apply_affine
    (f : (Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)) ⟶
      ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))) :
    (CharacterMap.Construction.affineCartierCharacterMap R A).app
      (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R))))
        (ULift.up f) = AffineCharacterValues.Construction.affineGroupLikeSection R S A
          (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A
            (Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R A) S f)) := by
  let e := Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R A) S
  obtain ⟨g, rfl⟩ := e.symm.surjective f
  have h := congrArg (fun h => AffineCharacterValues.Construction.affineGroupLikeSection R S A
    (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A h)) (e.apply_symm_apply g)
  exact (affineCartierCharacterMap_apply_algHom R S A g).trans h.symm

/-- Every affine component of the canonical character map is bijective. -/
theorem affineCartierCharacterMap_app_bijective :
    Function.Bijective ((CharacterMap.Construction.affineCartierCharacterMap R A).app
      (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R))))) := by
  have hs : Function.Bijective (AffineCharacterValues.Construction.affineGroupLikeSection R S A) :=
    (AffinePullback.Construction.affineGroupCharacterSectionsEquiv R S A).bijective.comp
      (Characters.Construction.groupLikeEquivSchemeCharacters S (S ⊗[R] A)).bijective
  have he := hs.comp ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).bijective.comp
    ((Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R A) S).bijective.comp
      Equiv.ulift.bijective))
  have hf : (fun f => (CharacterMap.Construction.affineCartierCharacterMap R A).app
      (Opposite.op ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))) f) =
      (AffineCharacterValues.Construction.affineGroupLikeSection R S A ∘ DualAlgebra.Construction.affineDualPointsEquivCharacters R S A ∘
        Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R A) S ∘ Equiv.ulift) := by
    apply funext
    rintro ⟨f⟩
    dsimp only [Function.comp_def, Equiv.ulift]
    exact affineCartierCharacterMap_apply_affine R S A f
  exact (congrArg Function.Bijective hf).mpr he

/-- The dual coordinate group represents the actual fppf character
sheaf on all test schemes over the affine base. -/
theorem affineCartierCharacterSheafMap_isIso :
    IsIso (CharacterMap.Construction.affineCartierCharacterSheafMap R A) := by
  apply (SheafDescent.Construction.sheafMap_isIso_iff_affine (CommRingCat.of R) _).mpr
  intro B
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  change Function.Bijective ((CharacterMap.Construction.affineCartierCharacterMap R A).app
    (Opposite.op ((Spec (CommRingCat.of B.unop)).asOver (Spec (CommRingCat.of R)))))
  exact affineCartierCharacterMap_app_bijective R B.unop A

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineSheafIso.Construction
