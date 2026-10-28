import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterDifferential
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SubmersionCoordinates

/-! # Parameter Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterCoordinates.Constructions

noncomputable section

/-!
# DegreeTwo: an actual regular divisor parameter is a complex normal coordinate

The algebraic point derivation and the analytic implicit function theorem
give genuine coordinates on the affine point space. The first coordinate
is exactly the regular section, with analytic evaluation in the inverse chart.
-/

open scoped ContDiff _root_.Topology

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.Smooth ℂ S]

/-- A smooth principal hypersurface is locally the zero hyperplane of its
own regular equation in genuine complex analytic coordinates. -/
theorem exists_parameter_normal_coordinates (p : S) (hp : p ≠ 0)
    [Algebra.FormallySmooth ℂ (S ⧸ Ideal.span {p})]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hxp : x p = 0) :
    ∃ (g : S) (n m : ℕ)
      (P : Algebra.SubmersivePresentation ℂ (Localization.Away g) (Fin n) (Fin m))
      (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))
      (q : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints S)
        (ℂ × (fderiv ℂ (fun z => e.symm z p) (e x)).ker)),
      x ∈ q.source ∧ q x = 0 ∧
      (∀ y ∈ q.source, (q y).1 = y p) ∧
      (∀ a : S, ContDiffOn ℂ ω (fun z => q.symm z a) q.target) := by
  obtain ⟨g, n, m, P, e, hx, hi, hs⟩ := ParameterDifferential.Constructions.exists_parameter_submersion_chart p hp x hxp
  have hf := (hi p).contDiffAt (e.open_target.mem_nhds (e.map_source hx))
  obtain ⟨r, hr, hrx, hrf, _, hri⟩ :=
    SubmersionCoordinates.Constructions.exists_analytic_submersion_coordinates (fun z => e.symm z p) (e x) hf hs
  refine ⟨g, n, m, P, e, e.trans r, ⟨hx, hr⟩, ?_, ?_, ?_⟩
  · change r (e x) = 0
    rw [hrx, e.left_inv hx, hxp]
    rfl
  · intro y hy
    change (r (e y)).1 = y p
    rw [hrf, e.left_inv hy.1]
  · intro a
    change ContDiffOn ℂ ω (fun z => e.symm (r.symm z) a)
      (r.target ∩ r.symm ⁻¹' e.target)
    exact (hi a).comp (hri.mono Set.inter_subset_left) (fun _ hz => hz.2)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ParameterCoordinates.Constructions
