import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LaurentNaturality

/-! # Unit Value Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection

noncomputable section

/-!
# CartierDuality: actual regular-unit values distinguish multiplicative-group points
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- The Laurent-generator value determines an integral multiplicative-group point on every scheme. -/
theorem integralUnitValue_injective (T : Over (Spec (.of (ULift.{u} ℤ)))) :
    Function.Injective (HopfScalarsOf.Construction.HopfScalars.groupLikeUnitHom (ULift.{u} ℤ)
      (Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)) CharacterUnitValues.Construction.Schemes.multiplicativeGroupGenerator T) := by
  intro x y h
  let C := Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ)
  let a : C →+* Γ(T.left, ⊤) := x.left.appTop.hom.comp (Scheme.ΓSpecIso (.of C)).inv.hom
  let b : C →+* Γ(T.left, ⊤) := y.left.appTop.hom.comp (Scheme.ΓSpecIso (.of C)).inv.hom
  have hab : a = b := LaurentNaturality.Construction.integralLaurentHom_ext (congrArg Units.val h)
  apply Over.OverMorphism.ext
  have : IsAffine ((Spec (.of C)).asOver (Spec (.of (ULift.{u} ℤ)))).left :=
    inferInstanceAs (IsAffine (Spec (.of C)))
  apply AlgebraicGeometry.ext_of_isAffine
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of C)).inv).surjective z
  exact (congrArg x.left.appTop hr).symm.trans ((RingHom.congr_fun hab r).trans (congrArg y.left.appTop hr))

/-- The natural regular-unit value detects equality of actual multiplicative-group points over any base. -/
theorem multiplicativeGroupUnitHom_injective {S : Scheme.{u}} (T : Over S) :
    Function.Injective (CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T) := by
  intro x y h
  apply (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv (specULiftZIsTerminal.from S) (Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)) T).symm.injective
  exact integralUnitValue_injective ((Over.map (specULiftZIsTerminal.from S)).obj T) h

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection
