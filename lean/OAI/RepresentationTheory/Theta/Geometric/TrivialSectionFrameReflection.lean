import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue

/-! # Trivial Section Frame Reflection -/

namespace OAI.RepresentationTheory.Theta.Geometric.TrivialSectionFrameReflection

noncomputable section

/-! On a trivial line bundle, a map on global functions that is an
isomorphism detects whether a section is a frame after pullback. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem trivialSection_isIso_of_pullback {X T : Scheme.{u}} (b : T ⟶ X) [IsIso b.appTop]
    {M : X.Modules} (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    [IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b s)] : IsIso s := by
  let v := s ≫ e.hom
  have hp : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b v) := by
    change IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b (s ≫ e.hom))
    rw [AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison.Construction.pullbackSection_targetMap]
    infer_instance
  have hi : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b v ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).hom) := by
    infer_instance
  have hu := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection b v ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).hom)).mp hi
  change IsUnit (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).inv ≫
    (Scheme.Modules.pullback b).map v ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso b).hom)) at hu
  rw [AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars.value_pullback] at hu
  have hc := hu.map (asIso b.appTop).inv.hom
  have he : (asIso b.appTop).inv (b.appTop (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X v)) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X v := (asIso b.appTop).hom_inv_id_apply _
  have hv : IsIso v := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff v).mpr (he ▸ hc)
  exact (isIso_comp_right_iff s e.hom).mp hv

end

end OAI.RepresentationTheory.Theta.Geometric.TrivialSectionFrameReflection
