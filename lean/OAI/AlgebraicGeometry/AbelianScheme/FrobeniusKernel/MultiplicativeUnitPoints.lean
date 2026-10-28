import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection

/-! # Multiplicative Unit Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitPoints

noncomputable section

/-! Every regular unit is an actual multiplicative-group point. This
identifies natural unit-valued kernel characters with scheme characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection.Construction.Schemes

def integralUnitCoordinateMap (R : Type u) [CommRing R] (a : Rˣ) :
    CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ) →+* R :=
  MonoidAlgebra.liftNCRingHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
    ((Units.coeHom R).comp (zpowersHom Rˣ a)) (fun _ _ => .all ..)

theorem integralUnitCoordinateMap_generator (R : Type u) [CommRing R] (a : Rˣ) :
    integralUnitCoordinateMap R a
      (MonoidAlgebra.of (ULift.{u} ℤ) (Multiplicative ℤ) (Multiplicative.ofAdd 1)) = a.val := by
  simp [integralUnitCoordinateMap, MonoidAlgebra.of_apply]

def integralUnitPoint (T : Over (Spec (.of (ULift.{u} ℤ)))) (a : Γ(T.left, ⊤)ˣ) :
    T ⟶ (CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X :=
  Over.homMk
    ((ΓSpec.adjunction.homEquiv T.left (.op (.of (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)))))
      (CommRingCat.ofHom (integralUnitCoordinateMap Γ(T.left, ⊤) a)).op)
    (specULiftZIsTerminal.hom_ext _ _)

theorem integralUnitPoint_value (T : Over (Spec (.of (ULift.{u} ℤ)))) (a : Γ(T.left, ⊤)ˣ) :
    CartierDuality.HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ) (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ))
      CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator T (integralUnitPoint T a) = a := by
  apply Units.ext
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
    (CommRingCat.ofHom (integralUnitCoordinateMap Γ(T.left, ⊤) a))
  exact (ConcreteCategory.congr_hom h
    (MonoidAlgebra.of (ULift.{u} ℤ) (Multiplicative ℤ) (Multiplicative.ofAdd 1))).trans
    (integralUnitCoordinateMap_generator Γ(T.left, ⊤) a)

theorem multiplicativeGroupUnitHom_surjective {S : Scheme.{u}} (T : Over S) :
    Function.Surjective (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T) := by
  intro a
  let p := specULiftZIsTerminal.from S
  let G := CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)
  let x := integralUnitPoint ((Over.map p).obj T) a
  refine ⟨CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T x, ?_⟩
  change CartierDuality.HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ)
    (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator
      ((Over.map p).obj T) ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T).symm (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv p G T x)) = a
  rw [MulEquiv.symm_apply_apply]
  exact integralUnitPoint_value ((Over.map p).obj T) a

def multiplicativeGroupUnitEquiv {S : Scheme.{u}} (T : Over S) :
    (T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) ≃* Γ(T.left, ⊤)ˣ :=
  MulEquiv.ofBijective (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T)
    ⟨CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T, multiplicativeGroupUnitHom_surjective T⟩

theorem multiplicativeGroupUnitEquiv_natural {S : Scheme.{u}} {T U : Over S}
    (t : U ⟶ T) (a : Γ(T.left, ⊤)ˣ) :
    t ≫ (multiplicativeGroupUnitEquiv T).symm a =
      (multiplicativeGroupUnitEquiv U).symm (Units.map t.left.appTop.hom a) := by
  apply (multiplicativeGroupUnitEquiv U).injective
  exact (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom_natural t ((multiplicativeGroupUnitEquiv T).symm a)).symm.trans
    ((congrArg (Units.map t.left.appTop.hom) ((multiplicativeGroupUnitEquiv T).apply_symm_apply a)).trans
      ((multiplicativeGroupUnitEquiv U).apply_symm_apply _).symm)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeUnitPoints
