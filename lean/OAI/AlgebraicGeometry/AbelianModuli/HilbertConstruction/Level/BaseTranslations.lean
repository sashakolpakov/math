import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations

/-! # Base Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ordered full-level labels give actual torsion translations over the multiplication morphism on every base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.fullLevelBaseTorsionPoints (level : A.FullLevel N) :
    ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* A.torsionPoints N (𝟙_ (Over S)) :=
  (level.hom.app (.op (𝟙_ (Over S)))).hom.comp
    (LocallyConstant.constMonoidHom.comp
      { toFun := ULift.down
        map_one' := rfl
        map_mul' := fun _ _ => rfl })

def Abelian.Schemes.AbelianScheme.fullLevelMultiplicationTranslation (level : A.FullLevel N)
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    Over.mk (A.multiplication N).left ⟶ Over.mk (A.multiplication N).left :=
  Over.homMk (A.basePointTranslation (A.fullLevelBaseTorsionPoints level i).val).left
    (congrArg Over.Hom.left (A.basePointTranslation_multiplication N
      (A.fullLevelBaseTorsionPoints level i).val (A.fullLevelBaseTorsionPoints level i).property))

theorem Abelian.Schemes.AbelianScheme.fullLevelMultiplicationTranslation_one (level : A.FullLevel N) :
    A.fullLevelMultiplicationTranslation level 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  have h := congrArg (fun a : A.torsionPoints N (𝟙_ (Over S)) => a.val)
    (A.fullLevelBaseTorsionPoints level).map_one
  exact congrArg (fun f : A.scheme ⟶ A.scheme => f.left)
    ((congrArg (A.basePointTranslation) h).trans A.basePointTranslation_one)

theorem Abelian.Schemes.AbelianScheme.fullLevelMultiplicationTranslation_comp (level : A.FullLevel N)
    (i j : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelMultiplicationTranslation level i ≫ A.fullLevelMultiplicationTranslation level j =
      A.fullLevelMultiplicationTranslation level (i * j) := by
  apply Over.OverMorphism.ext
  have h := congrArg (fun a : A.torsionPoints N (𝟙_ (Over S)) => a.val)
    ((A.fullLevelBaseTorsionPoints level).map_mul i j)
  exact congrArg (fun f : A.scheme ⟶ A.scheme => f.left) ((A.basePointTranslation_comp
    (A.fullLevelBaseTorsionPoints level i).val (A.fullLevelBaseTorsionPoints level j).val).trans
      (congrArg (A.basePointTranslation) h.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
