import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.TensorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFiniteCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Bundle Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange

noncomputable section

/-! Flat affine base change commutes with global sections of a line bundle on a quasi-compact scheme with affine diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem flat_lineBundleTensorComparison_isIso
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ⊤)) := by
  obtain ⟨k, U, hAff, hFrame, hCover⟩ := L.exists_finite_affine_frames
  let V : ULift.{u} (Fin k) → X.Opens := fun i => U i.down
  have hU : iSup V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hCover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  have hlocal (i : Pairwise (ULift.{u} (Fin k))) :
      IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ((Pairwise.diagram V).obj i))) := by
    cases i with
    | single i =>
      exact AffineOpen.TensorBaseChange.affineFrame_moduleTensorComparison_isIso H L.sheaf (U i.down) (hAff i.down) (hFrame i.down).some
    | pair i j =>
      exact AffineOpen.TensorBaseChange.affineFrame_moduleTensorComparison_isIso H L.sheaf (U i.down ⊓ U j.down)
        ((hAff i.down).inf (hAff j.down)) (L.frameRestrict inf_le_left (hFrame i.down).some)
  exact HilbertConstruction.Module.TensorFiniteCover.baseChangeModuleTensorComparison_isIso_of_finite_cover H L.sheaf V hU hlocal

theorem flat_lineBundleTensorComparison_bijective
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    Function.Bijective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ⊤)) := by
  exact (ConcreteCategory.isIso_iff_bijective _).mp (flat_lineBundleTensorComparison_isIso H L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange
