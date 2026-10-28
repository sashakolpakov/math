import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import OAI.AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Hom Kernel Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.HomKernelInjectivity

noncomputable section

/-! Additivity turns triviality of the actual Picard kernel into
separation of every pair of parameters on the same test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterPicardClass_injective_of_hom_kernel
    {A P T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P] (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (rho : (T ⟶ P) →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A T) (hrho : ∀ r, rho r = ParameterizedPicardClass.parameterPicardClass Q r)
    (hker : ∀ r : T ⟶ P, ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : T ⟶ P) → r = 1) :
    Function.Injective (fun r : T ⟶ P => ParameterizedPicardClass.parameterPicardClass Q r) := by
  intro a b hab
  have hrab : rho a = rho b := (hrho a).trans (hab.trans (hrho b).symm)
  have hz : rho (a * b⁻¹) = rho 1 := by
    rw [map_mul, map_inv, hrab, mul_inv_cancel, map_one]
  have hk : a * b⁻¹ = 1 := hker (a * b⁻¹)
    ((hrho (a * b⁻¹)).symm.trans (hz.trans (hrho 1)))
  exact mul_inv_eq_one.mp hk

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.HomKernelInjectivity
