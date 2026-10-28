import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSupportKernel

/-! # Open Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions

noncomputable section

/-! An affine open in the original variety gives a genuine open in
its projective self-product. The original diagonal support and its
actual stalk ideal restrict to the affine diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Support.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalSupportKernel.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImageStalkKernel.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)

def productOpenMap : pullback X.hom X.hom ⟶ (Ambient.Constructions.productVariety V V).carrier :=
  pullback.map X.hom X.hom V.structureMap V.structureMap j.left j.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    (by rw [Category.comp_id]; exact j.w.symm)
    (by rw [Category.comp_id]; exact j.w.symm)

instance productOpenMap_open [IsOpenImmersion j.left] : IsOpenImmersion (productOpenMap V X j) := by
  unfold productOpenMap
  infer_instance

@[reassoc]
theorem diagonal_productOpenMap :
    pullback.diagonal X.hom ≫ productOpenMap V X j = j.left ≫ (Ambient.Constructions.diagonal V).left := by
  apply pullback.hom_ext <;> simp [productOpenMap, Ambient.Constructions.diagonal, Category.assoc]

theorem diagonal_point (x : X.left) :
    productOpenMap V X j (pullback.diagonal X.hom x) = (Ambient.Constructions.diagonal V).left (j.left x) :=
  congrArg (fun f : X.left ⟶ (Ambient.Constructions.productVariety V V).carrier => f x) (diagonal_productOpenMap V X j)

variable [IsAffine X.left] [IsIntegral X.left] [IsOpenImmersion j.left]

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)

theorem diagonal_genericPoint :
    productOpenMap V X j (IntersectionGeometry.supportPoint (Affine.DiagonalSupportKernel.Constructions.geometricDiagonalSupport X)) =
      IntersectionGeometry.supportPoint (Support.Constructions.diagonalClosedSupport V) := by
  unfold Affine.DiagonalSupportKernel.Constructions.geometricDiagonalSupport Support.Constructions.diagonalClosedSupport
  rw [Closed.ImageStalkKernel.Constructions.imageClosure_genericPoint, Closed.ImageStalkKernel.Constructions.imageClosure_genericPoint, diagonal_point]
  exact congrArg (Ambient.Constructions.diagonal V).left (genericPoint_eq_of_isOpenImmersion j.left)

omit [IsAffine X.left] [IsIntegral X.left] [IsOpenImmersion j.left] in
theorem diagonal_mem (x : X.left) : productOpenMap V X j (pullback.diagonal X.hom x) ∈
    (Support.Constructions.diagonalClosedSupport V : Set (Ambient.Constructions.productVariety V V).carrier) := by
  rw [Support.Constructions.diagonalClosedSupport_coe, diagonal_point]
  exact ⟨j.left x, rfl⟩

theorem diagonal_kernel_map (x : X.left) :
    (StalkPrimeQuotient.Constructions.kernelPrime (Ambient.Constructions.productVariety V V).carrier (Support.Constructions.diagonalClosedSupport V)
      (productOpenMap V X j (pullback.diagonal X.hom x)) (diagonal_mem V X j x)).asIdeal.map
        ((productOpenMap V X j).stalkMap (pullback.diagonal X.hom x)).hom =
      (StalkPrimeQuotient.Constructions.kernelPrime (pullback X.hom X.hom) (Affine.DiagonalSupportKernel.Constructions.geometricDiagonalSupport X)
        (pullback.diagonal X.hom x) (Affine.DiagonalSupportKernel.Constructions.geometric_point_mem X x)).asIdeal :=
  Open.StalkSupport.Constructions.kernelPrime_map (productOpenMap V X j) (Affine.DiagonalSupportKernel.Constructions.geometricDiagonalSupport X) (Support.Constructions.diagonalClosedSupport V)
    (diagonal_genericPoint V X j) (pullback.diagonal X.hom x) (Affine.DiagonalSupportKernel.Constructions.geometric_point_mem X x)
    (diagonal_mem V X j x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions
