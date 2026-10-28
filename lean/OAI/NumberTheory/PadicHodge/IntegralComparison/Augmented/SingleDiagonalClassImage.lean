import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechSingleTopCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoefficientTop
import Mathlib.Data.Int.Order.Units

/-! # Single Diagonal Class Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleDiagonalClassImage

noncomputable section

/-! In the diagonal degree, the genuine single-coefficient map carries
the ordinary top class to the literal total residue with its original
interchange sign. No vanishing of the target complex is needed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechSingleTopCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {R : Type v} [CommRing R] [HasProducts.{u} (ModuleCat.{w} R)]
  (N : Cᵒᵖ ⥤ ModuleCat.{w} R) (g : ℕ) (hg : Fintype.card ι = g)
  (z : N.obj (op (AugmentedOrdered.CechCoordinates.topObject U g hg)))

def sourceClass := AugmentedOrdered.CechLargeTop.topTotalClass U (AugmentedOrdered.CechSingleTopCoordinates.coefficientSingle N g)
  g hg g (AugmentedOrdered.CechSingleTopCoordinates.singleValue U N g hg g z) (AugmentedOrdered.CechSingleTopCoordinates.singleValue_closed U N g hg g z)

theorem coordinates :
    (Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N g g).hom (sourceClass U N g hg z) =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g • AugmentedOrdered.CechTopClass.topClass U N g hg z := by
  have h := AugmentedOrdered.CechSingleTopCoordinates.topTotalClass_coordinates U N g hg g z (AugmentedOrdered.CechSingleTopCoordinates.singleValue_closed U N g hg g z)
  convert h using 1; rfl

theorem inverse :
    (Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N g g).inv (AugmentedOrdered.CechTopClass.topClass U N g hg z) =
      ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g • sourceClass U N g hg z := by
  let e := Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N g g
  let s := ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g
  have h : e.hom (s • sourceClass U N g hg z) = s • (s • AugmentedOrdered.CechTopClass.topClass U N g hg z) := by
    change e.hom ((s : ℤ) • sourceClass U N g hg z) = _
    rw [map_zsmul, coordinates]
    rfl
  rw [smul_smul, Int.units_mul_self, one_smul] at h
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  exact (ConcreteCategory.congr_hom e.inv_hom_id (AugmentedOrdered.CechTopClass.topClass U N g hg z)).trans h.symm

variable (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
  (a : AugmentedOrdered.CechSingleTopCoordinates.coefficientSingle N g ⟶ K)

def image := (a.f g).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) (AugmentedOrdered.CechSingleTopCoordinates.singleValue U N g hg g z)

omit [HasProducts (ModuleCat R)] in
theorem image_closed : (K.d g (g+1)).app (op (AugmentedOrdered.CechCoordinates.topObject U g hg)) (image U N g hg z K a) = 0 :=
  AugmentedOrdered.CechCoefficientTop.mapped_coefficient_closed U a g hg g
    (AugmentedOrdered.CechSingleTopCoordinates.singleValue U N g hg g z) (AugmentedOrdered.CechSingleTopCoordinates.singleValue_closed U N g hg g z)

theorem map_apply :
    homologyMap (AugmentedOrdered.CechCoefficientTop.totalMap U a) (g+g)
      ((Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U) N g g).inv (AugmentedOrdered.CechTopClass.topClass U N g hg z)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      AugmentedOrdered.CechLargeTop.topTotalClass U K g hg g (image U N g hg z K a)
        (image_closed U N g hg z K a) := by
  rw [inverse]
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun x =>
    ((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤˣ) : ℤ) • x)
    (AugmentedOrdered.CechCoefficientTop.topTotalClass_naturality U a g hg g
      (AugmentedOrdered.CechSingleTopCoordinates.singleValue U N g hg g z) (AugmentedOrdered.CechSingleTopCoordinates.singleValue_closed U N g hg g z))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.SingleDiagonalClassImage
