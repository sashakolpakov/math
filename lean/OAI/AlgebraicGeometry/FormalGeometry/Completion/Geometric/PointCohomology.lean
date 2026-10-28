import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointTopology
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SheafAcyclicity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality

/-! # Point Cohomology -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointCohomology.Construction

noncomputable section

/-!
# Completion: acyclicity of the geometric point

The positive-degree cohomology of any abelian sheaf on the pro-étale site
of an algebraically closed field vanishes. In particular this applies to
mathlib's integral ℓ-adic cohomology and its algebraic coefficient extension.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Positive-degree cohomology of every abelian sheaf on the geometric point
vanishes. -/
theorem geometricPoint_sheaf_cohomology_eq_zero
    (F : Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of K))) AddCommGrpCat.{u + 1})
    (n : ℕ) (x : F.H (n + 1)) : x = 0 :=
  SheafAcyclicity.Construction.sheaf_cohomology_eq_zero_of_coveringSieve_eq_top (PointTopology.Construction.geometricPointProEtIsTerminal K)
    (PointTopology.Construction.geometricPoint_coveringSieve_eq_top K) F n x

/-- Actual integral ℓ-adic cohomology of a geometric point vanishes in
positive degrees. -/
theorem geometricPoint_integralEllAdicCohomology_eq_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (x : (Spec (CommRingCat.of K)).EllAdicCohomology ℓ (n + 1)) : x = 0 :=
  geometricPoint_sheaf_cohomology_eq_zero K (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ _) n x

/-- Integral ℓ-adic cohomology of a geometric point is trivial in positive degrees. -/
instance geometricPoint_integralEllAdicCohomology_subsingleton
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Subsingleton ((Spec (CommRingCat.of K)).EllAdicCohomology ℓ (n + 1)) :=
  subsingleton_of_forall_eq 0 (geometricPoint_integralEllAdicCohomology_eq_zero K ℓ n)

/-- Extension to algebraically closed ℓ-adic coefficients preserves vanishing. -/
instance geometricPoint_algebraicEllAdicH1_subsingleton (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (Cohomology.Construction.EllAdicH1AlgebraicCoefficients ℓ (Spec (CommRingCat.of K))) := by
  unfold Cohomology.Construction.EllAdicH1AlgebraicCoefficients
  infer_instance

/-- Pullback through a geometric point is zero in actual H¹. -/
theorem algebraicEllAdicH1Pullback_through_geometricPoint
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (g : Spec (CommRingCat.of K) ⟶ Y) :
    CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (f ≫ g) = 0 := by
  rw [← CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_comp]
  apply LinearMap.ext
  intro x
  have hx : CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ g x = 0 := Subsingleton.elim _ _
  simp only [LinearMap.comp_apply, hx, map_zero, LinearMap.zero_apply]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointCohomology.Construction
