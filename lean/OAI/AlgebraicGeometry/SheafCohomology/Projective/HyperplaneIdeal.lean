/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SpaceHyperplane
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealInvertible

/-! # Hyperplane Ideal -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneIdeal.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal module of a coordinate hyperplane is invertible. This is the
concrete model of `O(-1)` on polynomial projective space. -/
theorem coordinateHyperplaneIdealModule_isInvertible (j : σ) :
    Invertible.Scheme.Modules.IsInvertible
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) := by
  classical
  let : IsClosedImmersion (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) :=
    SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_isClosedImmersion j
  let : QuasiCompact (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) := inferInstance
  apply IdealInvertible.idealModule_isInvertible_of_locallyPrincipal
  intro y
  have hy : y ∈ ⨆ i : σ, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
    rw [MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  refine ⟨U, hyi, ?_⟩
  by_cases hji : j = i
  · subst i
    refine ⟨1, ?_, Submonoid.one_mem _⟩
    rw [SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_ker_ideal_coordinateOpen_self,
      Ideal.span_singleton_one]
  · let r : Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩)
    refine ⟨r, ?_, ?_⟩
    · exact SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_ker_ideal_coordinateOpen_of_ne i j hji
    · let e := (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
          (SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
      change e (SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩) ∈
        nonZeroDivisors Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
      rw [← MulEquivClass.map_nonZeroDivisors e]
      exact ⟨SpaceChart.MvPolynomial.awayVar R i ⟨j, hji⟩, SpaceChart.MvPolynomial.awayVar_mem_nonZeroDivisors R i ⟨j, hji⟩, rfl⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneIdeal.MvPolynomial
