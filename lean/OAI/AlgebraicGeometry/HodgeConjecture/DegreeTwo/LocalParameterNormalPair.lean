import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalParameterCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EquationNormalPair

/-! # Local Parameter Normal Pair -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalParameterNormalPair.Constructions

noncomputable section

/-!
# DegreeTwo: normal pairs on the actual principal smooth divisor neighborhood

The tangent factor is placed in a finite complex coordinate space, and the
pair lies inside the same principal open on which smoothness was proved.
-/

open scoped ContDiff _root_.Topology

variable {S : Type} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- The actual parameter is the last coordinate of a finite-dimensional
complex chart inside its principal smooth neighborhood. -/
theorem exists_local_parameter_equationChart (p b : S) (hp : p ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxp : x p = 0) (hxb : x b ≠ 0) :
    ∃ (d : ℕ) (r : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) ((Fin d → ℂ) × ℂ)),
      x ∈ r.source ∧ r x = 0 ∧
      r.source ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b ∧
      ∀ y ∈ r.source, (r y).2 = y p := by
  obtain ⟨g, n, m, P, e, q, hxq, hqx, hqb, hq, _⟩ :=
    LocalParameterCoordinates.Constructions.exists_local_parameter_normal_coordinates p b hp x hxp hxb
  let D := (fderiv ℂ (fun z => e.symm z (algebraMap S (Localization.Away b) p))
    (e (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x b hxb))).ker
  let d := Module.finrank ℂ D
  let c : D ≃L[ℂ] (Fin d → ℂ) := (Module.finBasis ℂ D).equivFun.toContinuousLinearEquiv
  let k : (ℂ × D) ≃ₜ ((Fin d → ℂ) × ℂ) :=
    (Homeomorph.prodComm ℂ D).trans (c.toHomeomorph.prodCongr (Homeomorph.refl ℂ))
  let r := q.transHomeomorph k
  have hrx : r x = 0 := by
    change (c (q x).2, (q x).1) = 0
    rw [hqx]
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
    rfl
  exact ⟨d, r, hxq, hrx, hqb, hq⟩

/-- At every complex point in the proved smooth principal neighborhood,
the actual parameter is the normal coordinate of an actual full-support pair. -/
theorem exists_local_parameter_normalPair (p b : S) (hp : p ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span {p}) b))]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxp : x p = 0) (hxb : x b ≠ 0) :
    ∃ (d : ℕ) (N : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
      (Subtype.val : {y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S // y p = 0} → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) ⟨x, hxp⟩),
      N.neighborhood ⊆ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen b ∧
      ∀ y : N.neighborhood, N.normalCoordinate y = y.val p := by
  obtain ⟨d, r, hxr, hrx, hrb, hr⟩ := exists_local_parameter_equationChart p b hp x hxp hxb
  obtain ⟨N, hchart, hN⟩ := EquationNormalPair.Constructions.exists_equation_normalPair_with_chart (fun y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => y p)
    x hxp r hxr hrx hr
  refine ⟨d, N, ?_, hN⟩
  intro y hy
  have hs := N.neighborhood_subset_source hy
  rw [hchart] at hs
  exact hrb hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalParameterNormalPair.Constructions
