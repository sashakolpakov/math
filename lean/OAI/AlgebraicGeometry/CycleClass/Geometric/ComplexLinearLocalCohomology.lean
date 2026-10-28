import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearPuncturedHomotopy
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Complex Linear Local Cohomology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology.Cycles

noncomputable section

/-!
# Complex linear invariance of actual local cohomology

The proved path of invertible complex matrices acts on the entire vector
space and preserves its punctured complement at every time. It therefore
gives a homotopy of the actual pair `(ℂ^p, ℂ^p \ {0})`. The induced pullback
on genuine relative singular cohomology is the identity in every degree.
The construction includes `p = 0` and uses no orientation or purity theorem.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology
open scoped _root_.Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual ambient homotopy induced by the path of invertible matrices. -/
def complexMatrixAmbientHomotopy (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    TopCat.Homotopy (𝟙 (TopCat.of (ι → ℂ)))
      (TopCat.ofHom (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap A)) where
  toFun q := ComplexLinearHomotopy.Cycles.complexMatrixPath A hA q.1 *ᵥ q.2
  continuous_toFun :=
    ((ComplexLinearHomotopy.Cycles.complexMatrixPath A hA).continuous.comp continuous_fst).matrix_mulVec continuous_snd
  map_zero_left x := by simp
  map_one_left x := by simp [ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap]

/-- No nonzero vector reaches the puncture during the ambient homotopy. -/
theorem complexMatrixAmbientHomotopy_preservesPuncture
    (A : Matrix ι ι ℂ) (hA : IsUnit A) (t : unitInterval) :
    Set.MapsTo (fun x => complexMatrixAmbientHomotopy A hA (t, x))
      ({0}ᶜ : Set (ι → ℂ)) ({0}ᶜ : Set (ι → ℂ)) :=
  fun _ hx => PuncturedLinearHomotopy.Cycles.complexMatrix_mulVec_ne_zero _ (ComplexLinearHomotopy.Cycles.complexMatrixPath_isUnit A hA t) hx

/-- An invertible complex matrix induces the identity on actual local
cohomology, with any coefficient module and in every degree. -/
theorem complexMatrixLocalCohomologyMap_eq_id
    {R : Type} [Ring R] (M : ModuleCat.{0} R)
    (A : Matrix ι ι ℂ) (hA : IsUnit A) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (TopCat.ofHom (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap A))
      (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap_preservesPuncture A hA) n =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (ι → ℂ)) ({0}ᶜ : Set (ι → ℂ)) n) := by
  have h := RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy M
    (A := ({0}ᶜ : Set (ι → ℂ))) (B := ({0}ᶜ : Set (ι → ℂ)))
    (fun _ hx => hx) (ComplexLinearPuncturedHomotopy.Cycles.complexMatrixMap_preservesPuncture A hA)
    (complexMatrixAmbientHomotopy A hA)
    (complexMatrixAmbientHomotopy_preservesPuncture A hA) n
  simpa only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id] using h.symm

private theorem complexLinearMatrix_isUnit {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) :
    IsUnit (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap) :=
  LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr L.bijective)

/-- The ambient homotopy ends at the given continuous complex-linear map
itself, using its actual matrix in the standard coordinates. -/
def complexLinearAmbientHomotopy {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) :
    TopCat.Homotopy (𝟙 (TopCat.of (Fin p → ℂ)))
      (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
        (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom :=
  (complexMatrixAmbientHomotopy (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap)
    (complexLinearMatrix_isUnit L)).cast rfl (by
      apply ContinuousMap.ext
      intro x
      exact LinearMap.toMatrix'_mulVec L.toLinearEquiv.toLinearMap x)

theorem complexLinearAmbientHomotopy_preservesPuncture {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ)) (t : unitInterval) :
    Set.MapsTo (fun x => complexLinearAmbientHomotopy L (t, x))
      ({0}ᶜ : Set (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) :=
  complexMatrixAmbientHomotopy_preservesPuncture
    (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap) (complexLinearMatrix_isUnit L) t

/-- The identity theorem for the pullback induced by the actual continuous
complex-linear equivalence, with arbitrary coefficients. -/
theorem complexLinearLocalCohomologyMap_eq_id_withCoefficients
    {R : Type} [Ring R] (M : ModuleCat.{0} R) {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hL : Set.MapsTo L
      ({0}ᶜ : Set (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ))) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      (A := ({0}ᶜ : Set (Fin p → ℂ))) (B := ({0}ᶜ : Set (Fin p → ℂ)))
      (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
        (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom hL n =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) n) := by
  have h := RelativeCochainHomotopy.Cohomology.relativeSingularCohomologyMap_eq_of_homotopy M
    (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
    (f := 𝟙 (TopCat.of (Fin p → ℂ)))
    (g := (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
      (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom)
    (A := ({0}ᶜ : Set (Fin p → ℂ))) (B := ({0}ᶜ : Set (Fin p → ℂ)))
    (fun _ hx => hx) hL (complexLinearAmbientHomotopy L)
    (complexLinearAmbientHomotopy_preservesPuncture L) n
  simpa only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id] using h.symm

/-- In every degree, including in complex dimension zero, the actual rational
local cohomology pullback of an invertible complex-linear map is the identity. -/
theorem complexLinearLocalCohomologyMap_eq_id {p : ℕ}
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hL : Set.MapsTo L
      ({0}ᶜ : Set (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ))) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      (A := ({0}ᶜ : Set (Fin p → ℂ))) (B := ({0}ᶜ : Set (Fin p → ℂ)))
      (TopCat.isoOfHomeo (X := TopCat.of (Fin p → ℂ))
        (Y := TopCat.of (Fin p → ℂ)) L.toHomeomorph).hom hL n =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) n) :=
  complexLinearLocalCohomologyMap_eq_id_withCoefficients (ModuleCat.of ℚ ℚ) L hL n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology.Cycles
