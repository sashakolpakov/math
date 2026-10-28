import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DeRham

/-! # Form Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap

noncomputable section

/-!
# IntegralComparison: original-base frame forms map to the native relative form modules
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

abbrev frameModule (n : ℕ) : ModuleCat.{u} B := (Crystalline.DeRham.formsPresheaf f n).obj (op F)

abbrev compositeBase (U : C) : Algebra B (H.obj U).ring :=
  ((π.app U).ringMap.toRingHom.comp (Q.obj U).base).toAlgebra

def frameAlgebraMap (U : C) :
    letI : Algebra B F.ring := F.base.toAlgebra
    letI : Algebra B (H.obj U).ring := compositeBase H Q π U
    F.ring →ₐ[B] (H.obj U).ring := by
  letI : Algebra B F.ring := F.base.toAlgebra
  letI : Algebra B (H.obj U).ring := compositeBase H Q π U
  exact { (τ.app U).ringMap.toRingHom with
    commutes' b := (DFunLike.congr_fun (τ.app U).overBase b).trans
      (DFunLike.congr_fun (π.app U).overBase b).symm }

def map (U : C) (n : ℕ) : frameModule F n ⟶ RelativeCrystalline.ModuleMaps.formsModule H Q π U n := by
  letI : Algebra B F.ring := F.base.toAlgebra
  letI : Algebra B (Q.obj U).ring := (Q.obj U).base.toAlgebra
  letI : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  letI : Algebra B (H.obj U).ring := compositeBase H Q π U
  letI : IsScalarTower B (Q.obj U).ring (H.obj U).ring := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ModuleCat.ofHom (X := frameModule F n) (Y := RelativeCrystalline.ModuleMaps.formsModule H Q π U n)
    (PD.FormsCoefficientMap.formsMap B (Q.obj U).ring F.ring (H.obj U).ring F.ideal F.dividedPowers
      (H.obj U).ideal (H.obj U).dividedPowers (frameAlgebraMap H Q π F τ U) (τ.app U).ringMap.isDPMorphism n)

theorem map_symbol (U : C) (n : ℕ) (a : F.ring) (t : Fin n → F.ring) :
    letI : Algebra B F.ring := F.base.toAlgebra
    map H Q π F τ U n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B F.ring F.ideal F.dividedPowers a t) =
      RelativeCrystalline.FormData.symbol H Q π U n ((τ.app U).ringMap a) (fun i => (τ.app U).ringMap (t i)) := by
  let : Algebra B F.ring := F.base.toAlgebra
  let : Algebra B (Q.obj U).ring := (Q.obj U).base.toAlgebra
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  let : Algebra B (H.obj U).ring := compositeBase H Q π U
  let : IsScalarTower B (Q.obj U).ring (H.obj U).ring := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact PD.FormsCoefficientMap.formsMap_symbol B (Q.obj U).ring F.ring (H.obj U).ring F.ideal F.dividedPowers
    (H.obj U).ideal (H.obj U).dividedPowers (frameAlgebraMap H Q π F τ U) (τ.app U).ringMap.isDPMorphism n a t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap
