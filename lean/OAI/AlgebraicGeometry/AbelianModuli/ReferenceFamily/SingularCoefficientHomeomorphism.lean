import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
import OAI.AlgebraicTopology.Cohomology.Singular.Functor

/-! # Singular Coefficient Homeomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientHomeomorphism

noncomputable section

/-! Transfer coefficient lifting along an actual homeomorphism using the
original singular pullback maps. -/

open _root_.CategoryTheory

theorem singular_coefficient_surjective_of_homeomorph
    {R : Type} [Ring R] {M N : ModuleCat.{0} R} (f : M ⟶ N)
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (n : ℕ)
    (hf : Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X n)) :
    Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f Y n) := by
  let eM := AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv M e.toHomotopyEquiv n
  let eN := AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv N e.toHomotopyEquiv n
  intro a
  obtain ⟨b, hb⟩ := hf (eN.hom a)
  obtain ⟨c, hc⟩ := eM.toLinearEquiv.surjective b
  refine ⟨c, eN.toLinearEquiv.injective ?_⟩
  have hn := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Functor.coefficientMap_naturality f (TopCat.ofHom e.toHomotopyEquiv.toFun) n) c
  exact hn.symm.trans ((congrArg (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X n) hc).trans hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientHomeomorphism
