/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.ChartDifference

/-! # Compatible Coordinate Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} (D : Coordinate.SectionCover.CoordinateSectionCover X ι)

lemma Coordinate.SectionCover.CoordinateSectionCover.eq_of_coordinateChartExtension_self
    (M : X.Modules)
    (j : ι) (n : ℕ)
    (s t : Γ(M, D.opens j))
    (h :
      M.presheaf.map
          (homOfLE (D.overlap_le_left j j)).op t =
        X.presheaf.map
              (homOfLE (D.overlap_le_left j j)).op
              (D.ratio j j ^ n) •
          M.presheaf.map
            (homOfLE (D.overlap_le_right j j)).op s) :
    t = s := by
  let U := D.opens j
  let W := D.overlap j j
  have hWU : W = U := by
    dsimp only [W, U]
    rw [D.overlap_eq, inf_idem]
  let e : Γ(M, U) ≅ Γ(M, W) := M.presheaf.mapIso (eqToIso hWU).op
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have hleft : e.hom t =
      M.presheaf.map
        (homOfLE (D.overlap_le_left j j)).op t := by
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) t
  have hright : e.hom s =
      M.presheaf.map
        (homOfLE (D.overlap_le_right j j)).op s := by
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) s
  rw [hleft, h, D.ratio_self,
    one_pow, map_one, one_smul, ← hright]

/-- A quasicoherent section on one standard chart extends to a compatible
family of coefficients of some common homogeneous degree. -/
theorem Coordinate.SectionCover.CoordinateSectionCover.exists_compatible_coordinateCoefficients [Fintype ι]
    (M : X.Modules) [M.IsQuasicoherent]
    (j : ι) (s : Γ(M, D.opens j)) :
    ∃ (n : ℕ) (t : ∀ i : ι, Γ(M, D.opens i)),
      t j = s ∧ ∀ i k : ι,
        M.presheaf.map (homOfLE (D.overlap_le_left i k)).op (t i) =
        (D.transition i k :
          Γ(X, D.overlap i k)) ^ n •
          M.presheaf.map (homOfLE (D.overlap_le_right i k)).op (t k) := by
  obtain ⟨n, t, ht⟩ := Coordinate.SectionCover.CoordinateSectionCover.exists_coordinateChartExtension_forall D M j s
  obtain ⟨m, hm⟩ := Coordinate.SectionCover.CoordinateSectionCover.exists_pow_coordinateChartDifference_eq_zero_forall D M j n s t ht
  refine ⟨n + m, fun i => D.ratio i j ^ m • t i,
    ?_, fun i k => Coordinate.SectionCover.CoordinateSectionCover.coordinateChartExtensions_corrected_compatible
      D M i k j n m (t i) (t k) (hm i k)⟩
  dsimp only
  rw [D.ratio_self, one_pow, one_smul]
  exact Coordinate.SectionCover.CoordinateSectionCover.eq_of_coordinateChartExtension_self D M j n s (t j) (ht j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
