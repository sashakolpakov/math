import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointPairing

/-! # Pair Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pulling back Poincare evaluations and graph bundles along test-scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) {T U : Over S}

def Dual.Data.DualAbelianData.poincarePairPullbackIso (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) (h : U ⟶ T) :
    ((D.poincarePair f a).pullback h.left).sheaf ≅ (D.poincarePair (h ≫ f) (h ≫ a)).sheaf :=
  (Scheme.Modules.pullback h.left).mapIso (D.poincarePairDirectIso f a) ≪≫
    (Scheme.Modules.pullbackComp h.left (lift f a).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (comp_lift h f a))).app D.poincare.sheaf ≪≫
    (D.poincarePairDirectIso (h ≫ f) (h ≫ a)).symm

def Dual.Data.DualAbelianData.poincareGraphPullbackPairIso (p : A.scheme ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback a.left).sheaf ≅ (D.poincarePair (a ≫ p) a).sheaf := by
  have h : a.left ≫ (PoincareGraph.Bundles.poincareGraphMap D p).left = (lift (a ≫ p) a).left := by
    have he : a ≫ PoincareGraph.Bundles.poincareGraphMap D p = lift (a ≫ p) a := by
      simp only [PoincareGraph.Bundles.poincareGraphMap, comp_lift, Category.comp_id]
    exact congrArg Over.Hom.left he
  exact (Scheme.Modules.pullbackComp a.left (PoincareGraph.Bundles.poincareGraphMap D p).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫ (D.poincarePairDirectIso (a ≫ p) a).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
