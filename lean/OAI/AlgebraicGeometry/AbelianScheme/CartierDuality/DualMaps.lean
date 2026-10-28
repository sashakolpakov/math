import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.BaseChange

/-! # Dual Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualMaps.Construction

noncomputable section

/-!
# CartierDuality: functorial duality on coordinate morphisms

Dual morphisms are ordinary transposes. Their compatibility with the two
bialgebra structures, composition, bidual evaluation and scalar extension
is proved here, for use in gluing the affine construction.
-/

open _root_.Module TensorProduct Coalgebra

universe u v w w'

variable (R : Type u) [CommRing R]

section Transpose

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The transpose, with the convolution type synonym on both duals. -/
def dualCoordinateMap (f : M →ₗ[R] N) : DualAlgebra.Construction.DualCoordinate R N →ₗ[R] DualAlgebra.Construction.DualCoordinate R M :=
  (DualAlgebra.Construction.dualCoordinateLinearEquiv R M).symm.toLinearMap ∘ₗ f.dualMap ∘ₗ
    (DualAlgebra.Construction.dualCoordinateLinearEquiv R N).toLinearMap

@[simp]
theorem dualCoordinateMap_apply (f : M →ₗ[R] N) (g : DualAlgebra.Construction.DualCoordinate R N) (x : M) :
    dualCoordinateMap R f g x = g (f x) := rfl

end Transpose

section BaseChangeNaturality

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]
variable (S : Type w') [CommRing S] [Algebra R S]

/-- The arbitrary base-change comparison is natural in module maps. -/
theorem dualCoordinateBaseChange_natural (f : M →ₗ[R] N)
    (z : S ⊗[R] DualAlgebra.Construction.DualCoordinate R N) :
    DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R M S
      ((dualCoordinateMap R f).baseChange S z) =
    dualCoordinateMap S (f.baseChange S)
      (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R N S z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s g =>
    apply WithConv.ext
    apply AlgebraTensorModule.ext
    intro t x
    change DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R M S
      ((dualCoordinateMap R f).baseChange S (s ⊗ₜ[R] g)) (t ⊗ₜ[R] x) =
      dualCoordinateMap S (f.baseChange S)
        (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R N S (s ⊗ₜ[R] g)) (t ⊗ₜ[R] x)
    simp

end BaseChangeNaturality

variable {A : Type v} [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
variable [Module.Finite R A] [Module.Projective R A]
variable [Module.Finite R B] [Module.Projective R B]

local instance e56DualMapsInstance1 : CommRing (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convCommRing
local instance e56DualMapsInstance2 : Algebra R (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convAlgebra
local instance e56DualMapsInstance3 : CommRing (DualAlgebra.Construction.DualCoordinate R B) := LinearMap.convCommRing
local instance e56DualMapsInstance4 : Algebra R (DualAlgebra.Construction.DualCoordinate R B) := LinearMap.convAlgebra

omit [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B] in
theorem dualCoordinateTensor_map_eval (f : A →ₗ[R] B)
    (z : DualAlgebra.Construction.DualCoordinate R B ⊗[R] DualAlgebra.Construction.DualCoordinate R B) (x y : A) :
    DualAlgebra.Construction.dualCoordinateTensorEquiv R A A
      (TensorProduct.map (dualCoordinateMap R f) (dualCoordinateMap R f) z)
      (x ⊗ₜ[R] y) = DualAlgebra.Construction.dualCoordinateTensorEquiv R B B z (f x ⊗ₜ[R] f y) := by
  induction z using TensorProduct.inductionOn with
  | tmul g h => simp
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- Transposing a bialgebra map reverses its direction and preserves the
dual bialgebra structures. -/
def dualCoordinateBialgHom (f : A →ₐc[R] B) :
    DualAlgebra.Construction.DualCoordinate R B →ₐc[R] DualAlgebra.Construction.DualCoordinate R A where
  __ := dualCoordinateMap R f.toLinearMap
  map_one' := by
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    exact CoalgHomClass.counit_comp_apply f x
  map_mul' g h := by
    apply WithConv.ext
    exact LinearMap.convMul_comp_coalgHom_distrib g h f.toCoalgHom
  counit_comp := by
    apply LinearMap.ext
    intro g
    change g (f 1) = g 1
    rw [map_one]
  map_comp_comul := by
    apply LinearMap.ext
    intro g
    apply DualAlgebra.Construction.dualCoordinateTensor_ext
    intro x y
    change DualAlgebra.Construction.dualCoordinateTensorEquiv R A A
      (TensorProduct.map (dualCoordinateMap R f.toLinearMap)
        (dualCoordinateMap R f.toLinearMap) (DualAlgebra.Construction.dualCoordinateComul R B g))
      (x ⊗ₜ[R] y) =
      DualAlgebra.Construction.dualCoordinateTensorEquiv R A A
        (DualAlgebra.Construction.dualCoordinateComul R A (dualCoordinateMap R f.toLinearMap g)) (x ⊗ₜ[R] y)
    rw [dualCoordinateTensor_map_eval, DualAlgebra.Construction.dualCoordinateComul_apply,
      DualAlgebra.Construction.dualCoordinateComul_apply, dualCoordinateMap_apply]
    exact congrArg (fun b : B => g b) (f.map_mul x y).symm

omit [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B] in
@[simp]
theorem dualCoordinateBialgHom_apply (f : A →ₐc[R] B) (g : DualAlgebra.Construction.DualCoordinate R B) (x : A) :
    dualCoordinateBialgHom R f g x = g (f x) := rfl

omit [Coalgebra.IsCocomm R A] in
@[simp]
theorem dualCoordinateBialgHom_id :
    dualCoordinateBialgHom R (BialgHom.id R A) = BialgHom.id R (DualAlgebra.Construction.DualCoordinate R A) := by
  rfl

omit [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B] in
theorem dualCoordinateBialgHom_comp
    {C : Type w'} [CommRing C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Projective R C]
    (f : A →ₐc[R] B) (g : B →ₐc[R] C) :
    dualCoordinateBialgHom R (g.comp f) =
      (dualCoordinateBialgHom R f).comp (dualCoordinateBialgHom R g) := by
  rfl

/-- The bidual identification is natural in the original bialgebra. -/
theorem dualCoordinateBidual_natural (f : A →ₐc[R] B) (x : A) :
    dualCoordinateBialgHom R (dualCoordinateBialgHom R f)
      (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A x) =
        DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B (f x) := by
  rfl

/-- Dualization is fully faithful on finite projective commutative,
cocommutative bialgebras. The inverse is the transpose conjugated by
bidual evaluation, with both inverse laws proved. -/
def dualCoordinateBialgHomEquiv :
    (A →ₐc[R] B) ≃ (DualAlgebra.Construction.DualCoordinate R B →ₐc[R] DualAlgebra.Construction.DualCoordinate R A) where
  toFun := dualCoordinateBialgHom R
  invFun f := (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B).symm.toBialgHom.comp
    ((dualCoordinateBialgHom R f).comp (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A).toBialgHom)
  left_inv f := by
    apply BialgHom.ext
    intro x
    apply (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B).injective
    change DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B
      ((DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B).symm
        (dualCoordinateBialgHom R (dualCoordinateBialgHom R f)
          (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A x))) =
      DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B (f x)
    rw [BialgEquiv.apply_symm_apply]
    rfl
  right_inv f := by
    apply BialgHom.ext
    intro g
    apply WithConv.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun z : DualAlgebra.Construction.DualCoordinate R (DualAlgebra.Construction.DualCoordinate R B) => z g)
      ((DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R B).apply_symm_apply
        (dualCoordinateBialgHom R f (DualAlgebra.Construction.dualCoordinateBidualBialgEquiv R A x)))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualMaps.Construction
