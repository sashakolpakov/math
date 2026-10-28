import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.BoundedResolution
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.DirectSum.Basis

/-! # Complex Bounds -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ComplexBounds

noncomputable section

/-! The native tensor product of bounded complexes is bounded by the sum
of the bounds, and its terms are finite when the original terms are finite. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped Classical TensorProduct DirectSum

variable (R : Type) [CommRing R]
  (K L : ChainComplex (ModuleCat.{0} R) ℕ)

instance finite_antidiagonal (k : ℕ) : Finite {ij : ℕ × ℕ // ij.1 + ij.2 = k} := by
  apply Finite.of_injective
    (fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = k} =>
      ((⟨ij.val.1, by omega⟩, ⟨ij.val.2, by omega⟩) : Fin (k + 1) × Fin (k + 1)))
  intro a b h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : Fin (k + 1) × Fin (k + 1) => x.1.val) h)
    (congrArg (fun x : Fin (k + 1) × Fin (k + 1) => x.2.val) h)

def termIso (k : ℕ) :
    (HomologicalComplex.tensorObj K L).X k ≅
      ModuleCat.of R (⨁ ij : {ij : ℕ × ℕ // ij.1 + ij.2 = k},
        (K.X ij.val.1) ⊗[R] (L.X ij.val.2)) :=
  ModuleCat.coprodIsoDirectSum _

theorem finite_terms (hK : ∀ i, Module.Finite R (K.X i))
    (hL : ∀ i, Module.Finite R (L.X i)) (k : ℕ) :
    Module.Finite R ((HomologicalComplex.tensorObj K L).X k) := by
  let (i : ℕ) := hK i
  let (i : ℕ) := hL i
  exact Module.Finite.equiv (termIso R K L k).toLinearEquiv.symm

theorem free_terms (hK : ∀ i, Module.Free R (K.X i))
    (hL : ∀ i, Module.Free R (L.X i)) (k : ℕ) :
    Module.Free R ((HomologicalComplex.tensorObj K L).X k) := by
  let (i : ℕ) := hK i
  let (i : ℕ) := hL i
  exact Module.Free.of_equiv (termIso R K L k).toLinearEquiv.symm

theorem bounded (a b : ℕ) (hK : ∀ i, a < i → IsZero (K.X i))
    (hL : ∀ j, b < j → IsZero (L.X j)) (k : ℕ) (hk : a + b < k) :
    IsZero ((HomologicalComplex.tensorObj K L).X k) := by
  let Z (ij : {ij : ℕ × ℕ // ij.1 + ij.2 = k}) : ModuleCat.{0} R :=
    ModuleCat.of R ((K.X ij.val.1) ⊗[R] (L.X ij.val.2))
  have hz (ij : {ij : ℕ × ℕ // ij.1 + ij.2 = k}) : IsZero (Z ij) := by
    by_cases hi : a < ij.val.1
    · exact (tensorRight (L.X ij.val.2)).map_isZero (hK _ hi)
    · have hj : b < ij.val.2 := by omega
      exact (tensorLeft (K.X ij.val.1)).map_isZero (hL _ hj)
  have ht : IsZero (∐ Z) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro ij
    exact (hz ij).eq_of_src _ _
  change IsZero (∐ Z)
  exact ht

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ComplexBounds
