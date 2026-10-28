import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.LineDescent
import Mathlib.RingTheory.Flat.Equalizer

/-! # Presentation Flat Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.PresentationFlatDescent.Construction

noncomputable section

/-! Finite presentation, and hence invertibility, descends through a
faithfully flat ring map without a Noetherian assumption on the base. -/

open TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

theorem module_finitePresentation_of_faithfullyFlat_baseChange
    [Module.FaithfullyFlat R S] [Module.FinitePresentation S (S ⊗[R] M)] :
    Module.FinitePresentation R M := by
  have : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let fS := AlgebraTensorModule.lTensor S S f
  have hfS : Function.Surjective fS := (f.lTensor_surjective S hf)
  have hker : fS.ker.FG := Module.FinitePresentation.fg_ker fS hfS
  have : Module.Finite S fS.ker := Module.Finite.of_fg hker
  have : Module.Finite S (S ⊗[R] f.ker) :=
    Module.Finite.equiv (LinearMap.tensorKerEquiv S S f).symm
  have : Module.Finite R f.ker := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp inferInstance)

theorem module_invertible_of_faithfullyFlat_baseChange
    [Module.FaithfullyFlat R S] [Module.Invertible S (S ⊗[R] M)] : Module.Invertible R M := by
  have : Module.FinitePresentation S (S ⊗[R] M) := Module.finitePresentation_of_projective S (S ⊗[R] M)
  have : Module.FinitePresentation R M := module_finitePresentation_of_faithfullyFlat_baseChange R S M
  exact Picard.PoincareBundle.Affine.LineDescent.invertible_of_faithfullyFlat_baseChange R S M

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.PresentationFlatDescent.Construction
