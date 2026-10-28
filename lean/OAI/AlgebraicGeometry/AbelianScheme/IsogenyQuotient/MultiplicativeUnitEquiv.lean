import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection

/-! # Multiplicative Unit Equiv -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeUnitEquiv.Construction

noncomputable section

/-!
Regular units on any test scheme are exactly points of CartierDuality's actual
integral Hopf model of G_m. This supplies the inverse to its original
unit-value map, with no affineness or reducedness assumption on the test.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection.Construction.Schemes

universe u

def integralLaurentMapOfUnit {R : Type u} [CommRing R] (z : Rˣ) :
    CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ) →+* R :=
  MonoidAlgebra.liftNCRingHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
    ((Units.coeHom R).comp (zpowersHom Rˣ z)) (fun _ _ => Commute.all _ _)

theorem integralLaurentMapOfUnit_generator {R : Type u} [CommRing R] (z : Rˣ) :
    integralLaurentMapOfUnit z (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1)) = z := by
  simp [integralLaurentMapOfUnit, MonoidAlgebra.of_apply]

def integralMultiplicativePointOfUnit (T : Over (Spec (.of (ULift.{u} ℤ)))) (z : Γ(T.left, ⊤)ˣ) :
    T ⟶ (CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X :=
  Over.homMk (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (integralLaurentMapOfUnit z)))
    (specULiftZIsTerminal.hom_ext _ _)

theorem integralMultiplicativePointOfUnit_value
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (z : Γ(T.left, ⊤)ˣ) :
    CartierDuality.HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ)
      (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator T
      (integralMultiplicativePointOfUnit T z) = z := by
  apply Units.ext
  change T.left.toSpecΓ.appTop
    ((Spec.map (CommRingCat.ofHom (integralLaurentMapOfUnit z))).appTop
      (CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection _ (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1)))) = z.val
  rw [CartierDuality.HopfScalarsOf.Construction.HopfScalars.coordinateSection_pullback, integralLaurentMapOfUnit_generator]
  rw [Scheme.toSpecΓ_appTop]
  change (Scheme.ΓSpecIso Γ(T.left, ⊤)).hom ((Scheme.ΓSpecIso Γ(T.left, ⊤)).inv z.val) = z.val
  exact (Scheme.ΓSpecIso Γ(T.left, ⊤)).inv_hom_id_apply z.val

theorem multiplicativeGroupUnitHom_surjective {S : Scheme.{u}} (T : Over S) :
    Function.Surjective (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T) := by
  intro z
  let p := specULiftZIsTerminal.from S
  let G := CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)
  let x := integralMultiplicativePointOfUnit ((Over.map p).obj T) z
  refine ⟨CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T x, ?_⟩
  change CartierDuality.HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ)
    (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator ((Over.map p).obj T)
    ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T).symm (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T x)) = z
  rw [MulEquiv.symm_apply_apply]
  exact integralMultiplicativePointOfUnit_value ((Over.map p).obj T) z

def multiplicativeGroupUnitEquiv {S : Scheme.{u}} (T : Over S) :
    (T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) ≃* Γ(T.left, ⊤)ˣ :=
  MulEquiv.ofBijective (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T)
    ⟨CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T, multiplicativeGroupUnitHom_surjective T⟩

theorem multiplicativeGroupUnitEquiv_symm_natural
    {S : Scheme.{u}} {T U : Over S} (a : U ⟶ T) (z : Γ(T.left, ⊤)ˣ) :
    (multiplicativeGroupUnitEquiv U).symm (Units.map a.left.appTop.hom z) =
      a ≫ (multiplicativeGroupUnitEquiv T).symm z := by
  apply (multiplicativeGroupUnitEquiv U).injective
  rw [MulEquiv.apply_symm_apply]
  have hT : CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T ((multiplicativeGroupUnitEquiv T).symm z) = z :=
    (multiplicativeGroupUnitEquiv T).apply_symm_apply z
  have hv := CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom_natural a ((multiplicativeGroupUnitEquiv T).symm z)
  rw [hT] at hv
  exact hv

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeUnitEquiv.Construction
