import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamComplexMap

/-! # Change Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ChangeNaturality

noncomputable section

/-!
# IntegralComparison: frame section maps are natural under simultaneous diagram and frame changes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H K Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)
  (F G : BigCrystallineSite.Object p B J δ f) (α : G ⟶ F)
  (τ : H ⟶ (Functor.const C).obj G) (υ : K ⟶ (Functor.const C).obj F)
  (hτ : θ ≫ υ = τ ≫ (Functor.const C).map α)

def frameMap : ComplexMap.frameComplex F ⟶ ComplexMap.frameComplex G := by
  letI : Algebra B F.ring := F.base.toAlgebra
  letI : Algebra B G.ring := G.base.toAlgebra
  exact PD.DeRhamComplexMap.map (CommAlgCat.ofHom (Crystalline.DeRham.ambientMap f α))
    (Crystalline.DeRham.ambientMap_isDPMorphism f α)

include hτ in
theorem forms (U : C) (n : ℕ) :
    FormMap.map K Q ρ F υ U n ≫ Relative.DiagramFormMap.map H K Q π ρ θ hθ U n =
      (Crystalline.DeRham.formsPresheaf f n).map α.op ≫ FormMap.map H Q π G τ U n := by
  let : Algebra B F.ring := F.base.toAlgebra
  let : Algebra B G.ring := G.base.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply PD.FormsCoefficientMap.addHom_ext B F.ring F.ideal F.dividedPowers n
  intro a t
  change Relative.DiagramFormMap.map H K Q π ρ θ hθ U n
    (FormMap.map K Q ρ F υ U n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B F.ring F.ideal F.dividedPowers a t)) =
      FormMap.map H Q π G τ U n
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (Crystalline.DeRham.ambientMap f α))
          (Crystalline.DeRham.ambientMap_isDPMorphism f α) n
            (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B F.ring F.ideal F.dividedPowers a t))
  rw [FormMap.map_symbol, Relative.DiagramFormMap.map_symbol,
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol, FormMap.map_symbol]
  have he (x : F.ring) : (θ.app U).ringMap ((υ.app U).ringMap x) = (τ.app U).ringMap (α.ringMap x) :=
    congrArg (fun η : H ⟶ (Functor.const C).obj F => (η.app U).ringMap x) hτ
  exact congrArg₂ (RelativeCrystalline.FormData.symbol H Q π U n) (he a) (funext (fun i => he (t i)))

include hτ in
theorem complexes :
    ComplexMap.map K Q ρ F υ ≫ Relative.DiagramComplexMap.map H K Q π ρ θ hθ =
      ((Functor.const Cᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).map (frameMap F G α) ≫
        ComplexMap.map H Q π G τ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply NatTrans.ext
  funext U
  exact forms H K Q π ρ θ hθ F G α τ υ hτ U.unop n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ChangeNaturality
