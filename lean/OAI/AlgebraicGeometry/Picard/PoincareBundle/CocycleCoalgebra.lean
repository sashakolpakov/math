import OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleSwitchNext
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchCoalgebra

/-! # Cocycle Coalgebra -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleCoalgebra

noncomputable section

/-!
# Effective affine module descent from a gluing cocycle alone
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- A gluing cocycle with its actual ring-map scalar structures. -/
abbrev CocycleSwitch (M : ModuleCat.{u} S) :=
  let := f.toAlgebra
  let := Module.compHom M f
  let := SwitchCoalgebra.restrictedScalarTower f M
  CocycleSwitchNext.CocycleSwitch R S M

variable (M : ModuleCat.{u} S)

/-- The actual extension/restriction coaction extracted from gluing. -/
def coaction (D : CocycleSwitch f M) :
    M ⟶ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M := by
  letI := f.toAlgebra
  letI := Module.compHom M f
  letI := SwitchCoalgebra.restrictedScalarTower f M
  exact ofHom (Y := (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M) D.coaction

/-- The categorical counit law is derived from the gluing cocycle. -/
theorem coaction_counit (D : CocycleSwitch f M) :
    CocycleCoalgebra.coaction f M D ≫ (extendRestrictScalarsAdj.{u,u,u} f).counit.app M = 𝟙 M := by
  let := f.toAlgebra
  let := Module.compHom M f
  let := SwitchCoalgebra.restrictedScalarTower f M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change DescentSwitch.diagonal R S M (D.coaction m) = m
  exact D.counit m

/-- The categorical coassociativity law is derived from the gluing cocycle. -/
theorem coaction_coassoc (D : CocycleSwitch f M) :
    CocycleCoalgebra.coaction f M D ≫ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.δ.app M =
      CocycleCoalgebra.coaction f M D ≫ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.map
        (CocycleCoalgebra.coaction f M D) := by
  let := f.toAlgebra
  let := Module.compHom M f
  let := SwitchCoalgebra.restrictedScalarTower f M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change TensorProduct.map (LinearMap.id : S →ₗ[R] S)
      (DescentSwitch.unitMap R S M) (D.coaction m) =
    TensorProduct.map (LinearMap.id : S →ₗ[R] S)
      (D.coaction.restrictScalars R) (D.coaction m)
  exact (D.coassoc m).symm

/-- No counit, diagonal, or transposition condition is assumed in this coalgebra construction. -/
def moduleDatum (D : CocycleSwitch f M) : Affine.Descent.ModuleDatum f where
  A := M
  a := CocycleCoalgebra.coaction f M D
  counit := coaction_counit f M D
  coassoc := coaction_coassoc f M D

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleCoalgebra
