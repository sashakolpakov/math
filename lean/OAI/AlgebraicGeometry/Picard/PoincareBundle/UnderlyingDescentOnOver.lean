import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent

/-! # Underlying Descent On Over -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescentOnOver

noncomputable section

/-!
# Underlying ordinary descent retains its original values on objects over the base
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent

variable {C : Type u} [Category.{v} C] {S : C} {A B T : Over S} (f : A ⟶ B)

/-- The original test object maps canonically to the same underlying object with its quotient-induced structure. -/
def returnMap (q : T ⟶ B) : T ⟶ UnderlyingDescent.testObject q.left :=
  Over.homMk (𝟙 T.left) (by
    change (𝟙 T.left) ≫ (q.left ≫ B.hom) = T.hom
    rw [Category.id_comp, Over.w q])

/-- This canonical identity on underlying objects preserves the quotient test map. -/
theorem return_base (q : T ⟶ B) : returnMap q ≫ UnderlyingDescent.baseMap q.left = q :=
  Over.OverMorphism.ext (Category.id_comp q.left)

/-- It also preserves the actual source-cover test points. -/
theorem return_cover (q : T ⟶ B) (x : T ⟶ A) (hx : x ≫ f = q) :
    returnMap q ≫ UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit)
      q.left x.left (congrArg Over.Hom.left hx) = x :=
  Over.OverMorphism.ext (Category.id_comp x.left)

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  (D : (DescentReindexing.reindex (Over.forget S) F).DescentData (fun (_ : PUnit.{1}) => f))

/-- Forgetting the base and evaluating again on an original test object gives exactly its original descent morphism. -/
theorem hom_eq (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D).hom q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy := by
  let x₀ := UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q.left x.left (congrArg Over.Hom.left hx)
  let y₀ := UnderlyingDescent.coverMap (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) q.left y.left (congrArg Over.Hom.left hy)
  have hx₀ : x₀ ≫ f = UnderlyingDescent.baseMap q.left := UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) _ _ _
  have hy₀ : y₀ ≫ f = UnderlyingDescent.baseMap q.left := UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) _ _ _
  have hnat := D.pullHom_hom (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (returnMap q) (UnderlyingDescent.baseMap q.left) q (return_base q)
    x₀ y₀ hx₀ hy₀ x y (return_cover f q x hx) (return_cover f q y hy)
  have hr := DescentReindexing.pullHom_reindex (Over.forget S) F
    (D.hom (UnderlyingDescent.baseMap q.left) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x₀ y₀ hx₀ hy₀)
    (returnMap q) x y (return_cover f q x hx) (return_cover f q y hy)
  have he := hr.symm.trans hnat
  change pullHom (F := F)
    ((UnderlyingDescent.underlyingDatum F (fun (_ : PUnit.{1}) => f) D).hom q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy))
    (𝟙 T.left) x.left y.left _ _ = D.hom q x y hx hy at he
  rw [pullHom_id] at he
  exact he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescentOnOver
