import OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses

/-! # Rationalized Functional Ext -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalizedFunctionalExt.Constructions

noncomputable section

/-! Rational homology functionals are determined on actual integral cycle classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

theorem rationalizedHomology_functional_ext
    (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) {M : ModuleCat.{0} ℚ}
    (f g : (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj C).homology n ⟶ M)
    (h : ∀ z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n,
      f (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle C n 1 z)) =
        g (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle C n 1 z))) : f = g := by
  apply (cancel_epi (CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).inv).mp
  apply ModuleCat.ExtendScalars.hom_ext
  intro u
  obtain ⟨z,rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n u
  have hz : (CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).inv
      ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z)) =
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle C n 1 z) := by
    apply (ModuleCat.mono_iff_injective (CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).hom).mp inferInstance
    rw [Iso.inv_hom_id_apply, AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizeHomologyIso_chainClass]
  change f ((CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).inv
    ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z))) =
      g ((CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso C n).inv
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z)))
  rw [hz]
  exact h z

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RationalizedFunctionalExt.Constructions
