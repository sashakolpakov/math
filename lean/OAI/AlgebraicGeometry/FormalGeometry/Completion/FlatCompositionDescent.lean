import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability

/-! # Flat Composition Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatCompositionDescent.Construction

noncomputable section

/-! # Completion: flatness descends through a faithfully flat map on the source -/

open TensorProduct
open scoped TensorProduct

universe u v w

/-- If the total algebra is flat and faithfully flat over the intermediate algebra,
then the intermediate algebra is flat over the original base. -/
theorem flat_of_faithfullyFlat_composition (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ f hf
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T
    (AlgebraTensorModule.lTensor S S f)).mp
  let eM := AlgebraTensorModule.cancelBaseChange R S S T M
  let eN := AlgebraTensorModule.cancelBaseChange R S S T N
  have he : (AlgebraTensorModule.lTensor S S f).lTensor T =
      eN.symm.toLinearMap ∘ₗ (AlgebraTensorModule.lTensor S T f) ∘ₗ eM.toLinearMap := by
    ext
    simp [eM, eN]
  rw [he]
  exact eN.symm.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp eM.injective)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatCompositionDescent.Construction
