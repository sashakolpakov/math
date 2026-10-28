import OAI.RepresentationTheory.Theta.Geometric.PeriodPolarizationAutomorphy
import OAI.RepresentationTheory.Theta.Geometric.DoubledPeriodLattice

/-! # Double Lattice Automorphy -/

namespace OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy

noncomputable section

/-! On twice the lattice, the semicharacter disappears and RiemannProjectivity's factor
for half the Hermitian form is exactly the original polarization factor. -/

variable {L I V : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)
  (e : L →+ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

theorem latticeQuadraticRefinement_nsmul (n : ℕ) (l : L) :
    LatticeSemicharacter.latticeQuadraticRefinement b B (n • l) = (n : ℤ) ^ 2 * LatticeSemicharacter.latticeQuadraticRefinement b B l := by
  simp only [LatticeSemicharacter.latticeQuadraticRefinement, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  ring

theorem polarizationAutomorphy_double_lattice (l : L) (z : V) :
    PolarizationAutomorphy.polarizationAutomorphy b B e H (2 • l) z =
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy ((1 / 2 : ℂ) • H) (e (2 • l)) z := by
  unfold PolarizationAutomorphy.polarizationAutomorphy Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy
  rw [latticeQuadraticRefinement_nsmul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨2 * LatticeSemicharacter.latticeQuadraticRefinement b B l, ?_⟩
  simp only [LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

end

end OAI.RepresentationTheory.Theta.Geometric.DoubleLatticeAutomorphy
