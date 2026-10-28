import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product

/-! # Reduced Open Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedOpenMaps

noncomputable section

/-! Inclusions between actual family opens induce the canonical
inclusions of their reduced opens, over the original complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {U V : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens} (h : V ≤ U)

def dualReducedOpenMap : DualOpen.Product.dualReducedOpenOver X V ⟶ DualOpen.Product.dualReducedOpenOver X U :=
  Over.homMk (X.left.homOfLE ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono h)) (by
    change (X.left.homOfLE _ ≫ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι) ≫ X.hom = _
    rw [Scheme.homOfLE_ι]
    rfl)

theorem dualReducedOpenMap_inclusion :
    dualReducedOpenMap X h ≫ DualOpen.Product.dualReducedOpenInclusion X U = DualOpen.Product.dualReducedOpenInclusion X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedOpenMaps
