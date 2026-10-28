import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomCoefficientComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CanonicalMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

/-! # Hom Presheaf Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheafMap

noncomputable section

/-! Actual Koszul resolution maps act on the entire Hom coefficient
presheaf and commute with the literal scalar-extension cochain map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {n m : ℕ} (s : Fin n → R) (t : Fin m → R)
  (f : OrientedTopCohomology.koszul R s ⟶
    OrientedTopCohomology.koszul R t)

def map : KoszulPartial.Components.coefficient R P t ⟶ KoszulPartial.Components.coefficient R P s :=
  (HomCoefficientComplex.iso R (Fin m → R) (KoszulPartial.Fractions.modules R P)
    (GeneratorMatrix.equation R t)).inv ≫
  HomCoefficientFunctor.map R (KoszulPartial.Fractions.modules R P) f ≫
  (HomCoefficientComplex.iso R (Fin n → R) (KoszulPartial.Fractions.modules R P)
    (GeneratorMatrix.equation R s)).hom

omit [HasFiniteProducts C] in
theorem map_apply (q : ℕ) (a : Cᵒᵖ)
    (φ : (⋀[R]^q (Fin m → R)) →ₗ[R] P.obj a)
    (x : ⋀[R]^q (Fin n → R)) :
    (show (⋀[R]^q (Fin n → R)) →ₗ[R] P.obj a from ((map R P s t f).f q).app a φ) x =
      φ (f.f q x) := rfl

@[reassoc]
theorem scalars : KoszulPartial.CanonicalMap.scalarsMap R P t ≫
    AugmentedOrdered.CechForgetNaturality.ambientMap (map R P s t f) =
      DualComplexHomology.map R f ≫ KoszulPartial.CanonicalMap.scalarsMap R P s := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheafMap
