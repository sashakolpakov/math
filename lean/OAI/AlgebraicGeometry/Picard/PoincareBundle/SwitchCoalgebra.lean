import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent

/-! # Switch Coalgebra -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchCoalgebra

noncomputable section

/-!
# Ordinary affine descent switches give effective module descent for PoincareBundle
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The restricted module carries its canonical scalar tower. -/
theorem restrictedScalarTower (M : ModuleCat.{u} S) :
    letI := f.toAlgebra
    letI := Module.compHom M f
    IsScalarTower R S M := by
  let := f.toAlgebra
  let := Module.compHom M f
  exact ⟨fun r s m => mul_smul (f r) s m⟩

/-- Tensor descent data with the scalar structures supplied by the ring map. -/
abbrev SwitchDatum (M : ModuleCat.{u} S) :=
  let := f.toAlgebra
  let := Module.compHom M f
  let := restrictedScalarTower f M
  DescentSwitch.SwitchDatum R S M

variable (M : ModuleCat.{u} S)

/-- The tensor switch induces the actual extension/restriction coaction. -/
def coaction (D : SwitchDatum f M) :
    M ⟶ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M := by
  letI := f.toAlgebra
  letI := Module.compHom M f
  letI := restrictedScalarTower f M
  exact ofHom (Y := (extendRestrictScalarsAdj.{u,u,u} f).toComonad.obj M) D.coaction

/-- Its ordinary diagonal identity implies the categorical counit identity. -/
theorem coaction_counit (D : SwitchDatum f M) :
    SwitchCoalgebra.coaction f M D ≫ (extendRestrictScalarsAdj.{u,u,u} f).counit.app M = 𝟙 M := by
  let := f.toAlgebra
  let := Module.compHom M f
  let := restrictedScalarTower f M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change DescentSwitch.diagonal R S M (D.coaction m) = m
  exact D.counit m

/-- The ordinary three-factor cocycle implies categorical coassociativity. -/
theorem coaction_coassoc (D : SwitchDatum f M) :
    SwitchCoalgebra.coaction f M D ≫ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.δ.app M =
      SwitchCoalgebra.coaction f M D ≫ (extendRestrictScalarsAdj.{u,u,u} f).toComonad.map
        (SwitchCoalgebra.coaction f M D) := by
  let := f.toAlgebra
  let := Module.compHom M f
  let := restrictedScalarTower f M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change TensorProduct.map (LinearMap.id : S →ₗ[R] S)
      (DescentSwitch.unitMap R S M) (D.coaction m) =
    TensorProduct.map (LinearMap.id : S →ₗ[R] S)
      (D.coaction.restrictScalars R) (D.coaction m)
  exact (D.coassoc m).symm

/-- A switch satisfying the Čech identities gives a genuine comonad coalgebra. -/
def moduleDatum (D : SwitchDatum f M) :
    Affine.Descent.ModuleDatum f where
  A := M
  a := SwitchCoalgebra.coaction f M D
  counit := coaction_counit f M D
  coassoc := coaction_coassoc f M D

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchCoalgebra
