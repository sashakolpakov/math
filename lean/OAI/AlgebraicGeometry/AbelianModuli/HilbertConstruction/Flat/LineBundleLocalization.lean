import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.TensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange
import Mathlib.RingTheory.Flat.Localization

/-! # Line Bundle Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LineBundleLocalization

noncomputable section

/-! Localization of affine coefficients localizes the actual global sections of a line bundle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem localized_lineBundle_section_pullback
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (T : Submonoid Γ(S, ⊤))
    [IsLocalization T (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    IsLocalizedModule T
      ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f.appTop.hom L.sheaf).app (.op ⊤)).hom := by
  have : Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    IsLocalization.flat (Affine.TensorSectionComparison.morphismGlobalAlgebra g) T
  apply Localized.TensorComparison.isLocalizedModule_of_tensor_comparison (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) T
    ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f.appTop.hom L.sheaf).app (.op ⊤)).hom
    ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ⊤)).hom
  · exact BundleSectionBaseChange.flat_lineBundleTensorComparison_bijective H L
  · exact Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison_one H L.sheaf ⊤

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LineBundleLocalization
