import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexDeterminant
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Complex Determinant Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange

noncomputable section

/-! Determinant formulas commute with extension of scalars, using the
actual tensor-product complex and its native homology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.Module _root_.CategoryTheory
open scoped TensorProduct Classical

universe u v w

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

local instance : DecidableEq (ι ⊕ κ) := Classical.decEq _

theorem det_map (M : Matrix (ι ⊕ κ) (ι ⊕ κ) R) :
    (M.map (algebraMap R S)).det = algebraMap R S M.det := by
  simpa only [RingHom.mapMatrix_apply] using ((algebraMap R S).map_det M).symm

theorem coprod_matrix (f : A →ₗ[R] B) (t : C →ₗ[R] B)
    (a : Basis ι R A) (b : Basis (ι ⊕ κ) R B) (c : Basis κ R C) :
    LinearMap.toMatrix ((Algebra.TensorProduct.basis S a).prod
      (Algebra.TensorProduct.basis S c)) (Algebra.TensorProduct.basis S b)
        ((f.baseChange S).coprod (t.baseChange S)) =
      (LinearMap.toMatrix (a.prod c) b (f.coprod t)).map (algebraMap R S) := by
  ext i j
  cases j <;>
    simp [LinearMap.toMatrix_apply, LinearMap.coprod_apply]

def complex (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0) :
    ShortComplex (ModuleCat.{u} S) :=
  ShortComplex.moduleCatMk (f.baseChange S) (g.baseChange S) (by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_zero])

theorem order_comparison [IsDomain S] [IsPrincipalIdealRing S]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (t : C →ₗ[R] B) (hf : Function.Injective (f.baseChange S))
    (ht : Function.Injective ((g.comp t).baseChange S))
    (a : Basis ι R A) (b : Basis (ι ⊕ κ) R B) (c : Basis κ R C) :
    Ring.ord S (algebraMap R S (LinearMap.toMatrix (a.prod c) b (f.coprod t)).det) +
        Module.length S ((S ⊗[R] C) ⧸ (g.baseChange S).range) =
      Module.length S (complex R S f g h).homology +
        Ring.ord S (algebraMap R S (g.comp t).det) := by
  let : Module.Free R C := Module.Free.of_basis c
  let : Module.Finite R C := Module.Finite.of_basis c
  have ht' : Function.Injective ((g.baseChange S).comp (t.baseChange S)) := by
    rwa [← LinearMap.baseChange_comp]
  have he := ShortComplexDeterminant.native_order_comparison S (complex R S f g h)
    hf (t.baseChange S) ht'
    ((Algebra.TensorProduct.basis S a).prod (Algebra.TensorProduct.basis S c))
    (Algebra.TensorProduct.basis S b) (Algebra.TensorProduct.basis S c)
  change Ring.ord S (LinearMap.toMatrix
    ((Algebra.TensorProduct.basis S a).prod (Algebra.TensorProduct.basis S c))
      (Algebra.TensorProduct.basis S b)
        ((f.baseChange S).coprod (t.baseChange S))).det +
    Module.length S ((S ⊗[R] C) ⧸ (g.baseChange S).range) =
    Module.length S (complex R S f g h).homology +
    Ring.ord S ((g.baseChange S).comp (t.baseChange S)).det at he
  rw [← LinearMap.baseChange_comp, LinearMap.det_baseChange, coprod_matrix R S,
    det_map R S] at he
  exact he

theorem euler_eq [IsDomain S] [IsPrincipalIdealRing S]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (t : C →ₗ[R] B) (hf : Function.Injective (f.baseChange S))
    (ht : Function.Injective ((g.comp t).baseChange S))
    (a : Basis ι R A) (b : Basis (ι ⊕ κ) R B) (c : Basis κ R C) :
    ((Module.length S ((S ⊗[R] C) ⧸ (g.baseChange S).range)).toNat : ℚ) -
        ((Module.length S (complex R S f g h).homology).toNat : ℚ) =
      ((Ring.ord S (algebraMap R S (g.comp t).det)).toNat : ℚ) -
        ((Ring.ord S (algebraMap R S
          (LinearMap.toMatrix (a.prod c) b (f.coprod t)).det)).toNat : ℚ) := by
  let : Module.Free R C := Module.Free.of_basis c
  let : Module.Finite R C := Module.Finite.of_basis c
  have ht' : Function.Injective ((g.baseChange S).comp (t.baseChange S)) := by
    rwa [← LinearMap.baseChange_comp]
  have he := ShortComplexDeterminant.native_euler_eq S (complex R S f g h)
    hf (t.baseChange S) ht'
    ((Algebra.TensorProduct.basis S a).prod (Algebra.TensorProduct.basis S c))
    (Algebra.TensorProduct.basis S b) (Algebra.TensorProduct.basis S c)
  change ((Module.length S ((S ⊗[R] C) ⧸ (g.baseChange S).range)).toNat : ℚ) -
    ((Module.length S (complex R S f g h).homology).toNat : ℚ) =
    ((Ring.ord S ((g.baseChange S).comp (t.baseChange S)).det).toNat : ℚ) -
    ((Ring.ord S (LinearMap.toMatrix
      ((Algebra.TensorProduct.basis S a).prod (Algebra.TensorProduct.basis S c))
        (Algebra.TensorProduct.basis S b)
          ((f.baseChange S).coprod (t.baseChange S))).det).toNat : ℚ) at he
  rw [← LinearMap.baseChange_comp, LinearMap.det_baseChange, coprod_matrix R S,
    det_map R S] at he
  exact he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange
