import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex

/-! # Diagram Form Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramFormMap

noncomputable section

/-!
# IntegralComparison: relative form maps induced by morphisms of original crystalline diagrams
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H K Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q) (ρ : K ⟶ Q)
  (θ : H ⟶ K) (hθ : θ ≫ ρ = π)

def algebraMap (U : C) :
    letI : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
    letI : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
    (K.obj U).ring →ₐ[(Q.obj U).ring] (H.obj U).ring := by
  letI : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
  letI : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact { (θ.app U).ringMap.toRingHom with
    commutes' a := congrArg (fun τ : H ⟶ Q => (τ.app U).ringMap a) hθ }

def linearMap (U : C) (n : ℕ) :
    letI : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
    letI : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
    RelativeCrystalline.FormData.Forms K Q ρ U n →ₗ[(Q.obj U).ring] RelativeCrystalline.FormData.Forms H Q π U n := by
  letI : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
  letI : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (algebraMap H K Q π ρ θ hθ U))
    (θ.app U).ringMap.isDPMorphism n

def map (U : C) (n : ℕ) : RelativeCrystalline.ModuleMaps.formsModule K Q ρ U n ⟶
    RelativeCrystalline.ModuleMaps.formsModule H Q π U n := by
  letI : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
  letI : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact (ModuleCat.restrictScalars (Q.obj U).base).map
    (ModuleCat.ofHom (linearMap H K Q π ρ θ hθ U n))

theorem map_symbol (U : C) (n : ℕ) (a : (K.obj U).ring) (t : Fin n → (K.obj U).ring) :
    DiagramFormMap.map H K Q π ρ θ hθ U n (RelativeCrystalline.FormData.symbol K Q ρ U n a t) =
      RelativeCrystalline.FormData.symbol H Q π U n ((θ.app U).ringMap a) (fun i => (θ.app U).ringMap (t i)) := by
  let : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (CommAlgCat.ofHom (algebraMap H K Q π ρ θ hθ U))
    (θ.app U).ringMap.isDPMorphism n a t

theorem map_differential (U : C) (n : ℕ) (ω : RelativeCrystalline.FormData.Forms K Q ρ U n) :
    DiagramFormMap.map H K Q π ρ θ hθ U (n + 1) (RelativeCrystalline.FormMaps.differential K Q ρ U n ω) =
      RelativeCrystalline.FormMaps.differential H Q π U n (DiagramFormMap.map H K Q π ρ θ hθ U n ω) := by
  let : Algebra (Q.obj U).ring (K.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra K Q ρ U
  let : Algebra (Q.obj U).ring (H.obj U).ring := RelativeCrystalline.FormData.relativeAlgebra H Q π U
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_differential (CommAlgCat.ofHom (algebraMap H K Q π ρ θ hθ U))
    (θ.app U).ringMap.isDPMorphism n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramFormMap
