import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementParameterPullback

/-! # Polarization Subfunctor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationSubfunctor

noncomputable section

/-! On a fixed full-level parameter family, existence of a polarization
whose canonical graph has the prescribed power line bundle is a genuine
subfunctor on all test schemes. Representability of this subfunctor is a
separate remaining construction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} (M : Over S) {g N : ℕ} (δ : Fin g → ℕ)
variable (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (L : Line.Bundles.LineBundle F.abelian.scheme.left) (d : ℕ)

def GraphPowerPolarizationPoint {T : Over S} (y : T ⟶ M) : Prop :=
  Nonempty (PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback y.left)
    (L.pullback (pullback.fst F.abelian.scheme.hom y.left)) d)

def graphPowerPolarizationSubfunctor : Subfunctor (yoneda.obj M) where
  obj _ := {y | GraphPowerPolarizationPoint M δ F L d y}
  map f y hy := by
    obtain ⟨D⟩ := hy
    let c : Over.mk (f.unop ≫ y).left ⟶ Over.mk y.left := Over.homMk f.unop.left rfl
    exact ⟨D.parameterPullback c⟩

def graphPowerPolarizationFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (graphPowerPolarizationSubfunctor M δ F L d).toFunctor

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationSubfunctor
