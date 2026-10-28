/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Coordinate Compatible Extensions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateCompatibleExtensions.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A chart-extension equation on the self-overlap of `D₊(X j)` identifies
the two original sections, since `X j / X j = 1`. -/
lemma eq_of_coordinateChartExtension_self
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (n : ℕ)
    (s t : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
    (h :
      M.presheaf.map
          (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) j j)).op t =
        (Proj (homogeneousSubmodule σ R)).presheaf.map
              (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) j j)).op
              (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) j j ^ n) •
          M.presheaf.map
            (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) j j)).op s) :
    t = s := by
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let W := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) j j
  have hWU : W = U := by
    dsimp only [W, U]
    rw [CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq, inf_idem]
  let e : Γ(M, U) ≅ Γ(M, W) := M.presheaf.mapIso (eqToIso hWU).op
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have hleft : e.hom t =
      M.presheaf.map
        (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) j j)).op t := by
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) t
  have hright : e.hom s =
      M.presheaf.map
        (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) j j)).op s := by
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) s
  rw [hleft, h, CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self,
    one_pow, map_one, one_smul, ← hright]

/-- A quasicoherent section on one standard chart extends to a compatible
family of coefficients of some common homogeneous degree. -/
theorem exists_compatible_coordinateCoefficients [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (s : Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) :
    ∃ (n : ℕ) (t : ∀ i : σ, Γ(M, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)),
      t j = s ∧ ∀ i k : σ,
        M.presheaf.map (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op (t i) =
        (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) ^ n •
          M.presheaf.map (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op (t k) := by
  obtain ⟨n, t, ht⟩ := CoordinateExtensions.MvPolynomial.exists_coordinateChartExtension_forall M j s
  obtain ⟨m, hm⟩ := CoordinateExtensions.MvPolynomial.exists_pow_coordinateChartDifference_eq_zero_forall M j n s t ht
  refine ⟨n + m, fun i => CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j ^ m • t i,
    ?_, fun i k => CoordinateExtensions.MvPolynomial.coordinateChartExtensions_corrected_compatible
      M i k j n m (t i) (t k) (hm i k)⟩
  dsimp only
  rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self, one_pow, one_smul]
  exact eq_of_coordinateChartExtension_self M j n s (t j) (ht j)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateCompatibleExtensions.MvPolynomial
