import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.InverseSectionFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight

/-! # Line Bundle Rational Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleRationalFrames

noncomputable section

/-! On a connected reduced proper scheme over a field, a section of a trivial line bundle is a global frame if it is a frame at one rational point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem trivialLineBundle_section_isIso_of_rationalFiber
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (L : Line.Bundles.LineBundle X) (e : L.sheaf ≅ Line.Bundles.structureModule X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso (Ample.LineBundles.pullbackSection x s)] : IsIso s := by
  let M := Line.Bundles.LineBundle.trivial X
  let t : Line.Bundles.structureModule X ⟶ M.sheaf := 𝟙 _
  have : IsIso (Ample.LineBundles.pullbackSection x t) := by
    apply (Section.Nonvanishing.isIso_pullbackSection_iff x t).mpr
    change IsIso ((Scheme.Modules.pullback x).map (𝟙 (Line.Bundles.structureModule X)))
    infer_instance
  let e' : (L.tensor M).sheaf ≅ Line.Bundles.structureModule X := Tensor.UnitRight.tensorModuleUnitRightIso L.sheaf ≪≫ e
  exact (Tensor.InverseSectionFrames.tensorInverse_sections_frames_of_rationalFiber p x hx L M e' s t).1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleRationalFrames
