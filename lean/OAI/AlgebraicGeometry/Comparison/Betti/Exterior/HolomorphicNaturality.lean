import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientLinearity
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenNaturality

/-! # Holomorphic Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.HolomorphicNaturality

noncomputable section

/-! The actual exterior-module realization commutes with Zariski restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem exteriorToHolomorphicFormMap_restrict {U V : X.left.Opens} (h : V ≤ U) (n : ℕ)
    (a : ⋀[Γ(X.left, U)]^n Ω[Γ(X.left, U)⁄ℂ]) :
    Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap X V n
        (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap
          (CommAlgCat.ofHom (Algebraic.Sheaves.sectionRestriction X (homOfLE h).op)) n a) =
      Holomorphic.HolomorphicPullback.pullback (Opens.inclusion (Open.SmoothForms.analyticOpen_mono X h))
        (contMDiff_inclusion (I := 𝓘(ℂ, RegularSmoothness.NativeModel X)) (Open.SmoothForms.analyticOpen_mono X h)) n
        (Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap X U n a) := by
  obtain ⟨b, rfl⟩ := (Forms.exteriorFormsEquiv Γ(X.left, U) n).surjective a
  rw [← Forms.exteriorFormsEquiv_naturality,
    Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap_normalization, Holomorphic.CoefficientLinearity.exteriorToHolomorphicFormMap_normalization]
  exact CategoryTheory.congr_fun
    (HomologicalComplex.congr_hom (Holomorphic.OpenNaturality.openHolomorphicCochainMap_restrict X h) n) b

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.HolomorphicNaturality
