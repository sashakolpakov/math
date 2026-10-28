import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.Cech
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Cech Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor

noncomputable section

/-! Functoriality of the genuine augmented ordered Čech complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]

def objectMap {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (n : ℕ) : Cech.object U P n ⟶ Cech.object U Q n :=
  ((FormalCoproduct.evalOp C D).map f).app (op (Cech.formal U n))

omit [Preadditive D] in
theorem objectMap_coface {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (n : ℕ) (k : Fin (n + 1)) :
    objectMap U f n ≫ Cech.coface U Q n k = Cech.coface U P n k ≫ objectMap U f (n + 1) :=
  (((FormalCoproduct.evalOp C D).map f).naturality (Cech.face U n k).op).symm

theorem objectMap_differential {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) (n : ℕ) :
    objectMap U f n ≫ Cech.differential U Q n = Cech.differential U P n ≫ objectMap U f (n + 1) := by
  simp only [Cech.differential, comp_sum, sum_comp, comp_zsmul, zsmul_comp, objectMap_coface]

def complexMap {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) : Cech.complex U P ⟶ Cech.complex U Q :=
  CochainComplex.ofHom (fun n => objectMap U f n) (fun n => by
    dsimp only [Cech.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact objectMap_differential U f n)

def functor : (Cᵒᵖ ⥤ D) ⥤ CochainComplex D ℕ where
  obj := Cech.complex U
  map := complexMap U
  map_id P := by
    apply HomologicalComplex.Hom.ext
    funext n
    change ((FormalCoproduct.evalOp C D).map (𝟙 P)).app (op (Cech.formal U n)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change ((FormalCoproduct.evalOp C D).map (f ≫ g)).app (op (Cech.formal U n)) = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

instance additive : (functor U (D := D)).Additive where
  map_add {P Q} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (Limits.Pi.map (fun i : Cech.Index ι n => (f + g).app (op ((Cech.formal U n).obj i)))) =
      Limits.Pi.map (fun i : Cech.Index ι n => f.app (op ((Cech.formal U n).obj i))) +
        Limits.Pi.map (fun i : Cech.Index ι n => g.app (op ((Cech.formal U n).obj i)))
    apply Pi.hom_ext
    intro i
    simp only [Pi.map_π, add_comp]
    exact Preadditive.comp_add _ _ _
      (Pi.π (fun j : Cech.Index ι n => P.obj (op ((Cech.formal U n).obj j))) i)
      (f.app (op ((Cech.formal U n).obj i))) (g.app (op ((Cech.formal U n).obj i)))

def bicomplex (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) :
    HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  ((functor U).mapHomologicalComplex (.up ℕ)).obj K

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
