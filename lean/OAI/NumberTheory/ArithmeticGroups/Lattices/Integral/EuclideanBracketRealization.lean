import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BilinearCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.Killing
import OAI.NumberTheory.ArithmeticGroups.Lattices.CovolumeTransport

/-! # Euclidean Bracket Realization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.EuclideanBracketRealization.Construction

noncomputable section

/-! A full integral bracket lattice has Euclidean coordinates in which
the coordinate lattice and all bracket coefficients are integral. -/

open Set _root_.Module
open scoped Classical

theorem integral_lattice_bilinear_euclidean_coordinates
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (Λ : Submodule ℤ L) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (B : L →L[ℝ] L →L[ℝ] L)
    (hB : ∀ x ∈ Λ, ∀ y ∈ Λ, B x y ∈ Λ) :
    ∃ (m : ℕ) (e : L ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      Λ.map (e.toLinearMap.restrictScalars ℤ) =
        Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin m) ℝ)) ∧
      Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        (Positive.Killing.Construction.continuousBracketTransport e B) ∈ RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m) := by
  let m := Module.finrank ℤ Λ
  let bZ := Module.finBasis ℤ Λ
  let b := bZ.ofZLatticeBasis ℝ
  let b₀ := EuclideanSpace.basisFun (Fin m) ℝ
  let e := (b.equiv b₀.toBasis (Equiv.refl _)).toContinuousLinearEquiv
  have he (i : Fin m) : e (b i) = b₀ i := by
    exact Basis.equiv_apply b i b₀.toBasis (Equiv.refl _)
  have hmap : Λ.map (e.toLinearMap.restrictScalars ℤ) = Submodule.span ℤ (Set.range b₀) := by
    rw [← bZ.ofZLatticeBasis_span ℝ, Submodule.map_span, ← Set.range_comp]
    change Submodule.span ℤ (Set.range (fun i : Fin m => e (b i))) = _
    rw [show (fun i : Fin m => e (b i)) = b₀ from funext he]
  refine ⟨m, e, hmap, (BilinearCoordinates.Construction.integral_bilinear_coordinates_iff b₀.toBasis _).mpr ?_⟩
  intro i j
  have hei (r : Fin m) : e.symm (b₀ r) = (bZ r).val := by
    rw [← he, e.symm_apply_apply]
    exact bZ.ofZLatticeBasis_apply ℝ Λ r
  change e (B (e.symm (b₀ i)) (e.symm (b₀ j))) ∈ Submodule.span ℤ (Set.range b₀)
  rw [hei, hei, ← hmap]
  exact ⟨B (bZ i).val (bZ j).val, hB _ (bZ i).property _ (bZ j).property, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.EuclideanBracketRealization.Construction
