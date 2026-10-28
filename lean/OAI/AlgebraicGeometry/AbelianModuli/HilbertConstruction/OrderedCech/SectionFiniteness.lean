import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AugmentationInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroKernel

/-! # Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SectionFiniteness

noncomputable section

/-! Finite degree-zero Čech cohomology implies finite global sections over a Noetherian coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem coefficient_sections_finite_of_cech (hU : ∀ x : X, ∃ i, x ∈ U i)
    [Module.Finite R ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).homology 0)] :
    Module.Finite R ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤)) := by
  have : Module.Finite R ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).d 0 1).hom.ker :=
    Module.Finite.equiv (Cochain.ZeroKernel.cochainZeroHomologyKernelEquiv (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U))
  exact Module.Finite.of_injective (Augmentation.orderedCechSectionToCycles c M U)
    (AugmentationInjectivity.orderedCechSectionToCycles_injective c M U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SectionFiniteness
