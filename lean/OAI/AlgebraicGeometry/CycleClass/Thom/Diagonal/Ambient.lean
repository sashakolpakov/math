import OAI.AlgebraicGeometry.CycleClass.Thom.SegreClosed
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Image
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport

/-! # Ambient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions

noncomputable section

/-! The genuine smooth projective self-product and diagonal, together
with the original reduced diagonal images of cycle supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.SegreClosed.Constructions.ProjectiveProducts OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev productVariety (V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  SegreClosed.Constructions.ProjectiveProducts.tensorIntegralProjectiveVariety V W

def first (V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : (productVariety V W).toOver ⟶ V.toOver := fst V.toOver W.toOver
def second (V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : (productVariety V W).toOver ⟶ W.toOver := snd V.toOver W.toOver

def productLimit (V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IsLimit (BinaryFan.mk (first V W) (second V W)) :=
  tensorProductIsBinaryProduct V.toOver W.toOver

theorem product_dimension (V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (productVariety V W).complexDimension = V.complexDimension + W.complexDimension := by
  simp only [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension]
  let : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
  let : IsIntegral W.toOver.left := inferInstanceAs (IsIntegral W.carrier)
  let : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)
  let : LocallyOfFiniteType W.toOver.hom := inferInstanceAs (LocallyOfFiniteType W.structureMap)
  exact Scheme.ProductDimension.Constructions.schemeProduct_dimension V.toOver W.toOver

def diagonal (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : V.toOver ⟶ (productVariety V V).toOver :=
  Over.homMk (pullback.diagonal V.structureMap) (by
    change pullback.diagonal V.structureMap ≫ (pullback.fst V.structureMap V.structureMap ≫ V.structureMap) = _
    simp only [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
    rfl)

instance diagonal_closed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IsClosedImmersion (Constructions.diagonal V).left :=
  inferInstanceAs (IsClosedImmersion (pullback.diagonal V.structureMap))

@[reassoc]
theorem diagonal_first (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Constructions.diagonal V ≫ first V V = 𝟙 V.toOver := by
  apply Over.OverMorphism.ext
  exact pullback.diagonal_fst V.structureMap

@[reassoc]
theorem diagonal_second (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Constructions.diagonal V ≫ second V V = 𝟙 V.toOver := by
  apply Over.OverMorphism.ext
  exact pullback.diagonal_snd V.structureMap

theorem diagonal_degree (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    p + (productVariety V V).complexDimension = (p + V.complexDimension) + V.complexDimension := by
  rw [product_dimension]
  omega

def diagonalSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Geometric.DimensionCycles.DimensionCycleSupport (productVariety V V) (p + V.complexDimension) :=
  Closed.Image.Constructions.closedImageCycleSupport (Constructions.diagonal V) p (p + V.complexDimension) (diagonal_degree V p) Z

theorem diagonalSupport_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ((diagonalSupport V p Z).val : Set (productVariety V V).carrier) = (Constructions.diagonal V).left '' (Z.val : Set V.carrier) :=
  ProperImage.Reduction.Constructions.imageSupport_eq_image (Constructions.diagonal V) (inferInstance : IsProper (Constructions.diagonal V).left) Z

theorem diagonalSupport_genericPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (diagonalSupport V p Z).genericPoint = (Constructions.diagonal V).left Z.genericPoint :=
  Closed.Image.Constructions.closedImageCycleSupport_genericPoint (Constructions.diagonal V) p (p + V.complexDimension) (diagonal_degree V p) Z

theorem diagonalSupport_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Function.Injective (diagonalSupport V p) :=
  Closed.Image.Constructions.closedImageCycleSupport_injective (Constructions.diagonal V) p (p + V.complexDimension) (diagonal_degree V p)

theorem diagonal_product_preimage (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q) :
    (Constructions.diagonal V).left ⁻¹' ((Integral.ProductSupport.Constructions.integralProductSupport V V (productVariety V V) (first V V) (second V V)
      (productLimit V V) p q A B).val : Set (productVariety V V).carrier) =
        (A.val : Set V.carrier) ∩ (B.val : Set V.carrier) := by
  rw [Integral.ProductSupport.Constructions.integralProductSupport, Product.SupportScheme.Constructions.productIrreducibleSupport_coe]
  ext x
  change ((first V V).left ((Constructions.diagonal V).left x) ∈ (A.val : Set V.carrier) ∧
    (second V V).left ((Constructions.diagonal V).left x) ∈ (B.val : Set V.carrier)) ↔ _
  have h₁ : (first V V).left ((Constructions.diagonal V).left x) = x :=
    congrArg (fun f : V.toOver ⟶ V.toOver => f.left x) (diagonal_first V)
  have h₂ : (second V V).left ((Constructions.diagonal V).left x) = x :=
    congrArg (fun f : V.toOver ⟶ V.toOver => f.left x) (diagonal_second V)
  constructor
  · intro hx
    exact ⟨h₁ ▸ hx.1, h₂ ▸ hx.2⟩
  · intro hx
    exact ⟨h₁.symm ▸ hx.1, h₂.symm ▸ hx.2⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions
