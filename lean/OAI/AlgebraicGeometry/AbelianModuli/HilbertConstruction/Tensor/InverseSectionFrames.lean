import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberEndRing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionNonvanishing

/-! # Inverse Section Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.InverseSectionFrames

noncomputable section

/-! Sections of inverse line bundles which are both frames at a rational point are global frames on a connected reduced proper scheme. The inverse pairing and the rational-fiber maps are the actual sheaf maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem tensorInverse_sections_frames_of_rationalFiber
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (L M : Line.Bundles.LineBundle X) (e : (L.tensor M).sheaf ≅ Line.Bundles.structureModule X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (t : Line.Bundles.structureModule X ⟶ M.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection x s)] [IsIso (Ample.LineBundles.pullbackSection x t)] :
    IsIso s ∧ IsIso t := by
  let F := Scheme.Modules.pullback x
  let e' : ProductSheaf.tensorModule L.sheaf M.sheaf ≅ Line.Bundles.structureModule X := e
  let q : End (Line.Bundles.structureModule X) := ProductSections.tensorProductSection s t ≫ e'.hom
  have hp : IsIso (Ample.LineBundles.pullbackSection x (ProductSections.tensorProductSection s t)) :=
    (SectionNonvanishing.tensorProductSection_pullback_isIso_iff x L M s t).mpr
      ⟨inferInstance, inferInstance⟩
  have : IsIso (F.map (ProductSections.tensorProductSection s t)) :=
    (Section.Nonvanishing.isIso_pullbackSection_iff x (ProductSections.tensorProductSection s t)).mp hp
  have hq : IsIso (F.map q) := by
    change IsIso (F.map (ProductSections.tensorProductSection s t ≫ e'.hom))
    rw [F.map_comp]
    infer_instance
  let r := (Line.Bundles.LineBundle.trivial X).rationalFiberEndRingEquiv p x hx
  have hu : IsUnit (r q) := (isUnit_iff_isIso _).mpr hq
  have hqu : IsUnit q := by
    have h := hu.map r.symm.toRingHom
    change IsUnit (r.symm (r q)) at h
    exact (r.symm_apply_apply q) ▸ h
  have hqiso : IsIso q := (isUnit_iff_isIso q).mp hqu
  have hprod : IsIso (ProductSections.tensorProductSection s t) :=
    (isIso_comp_right_iff (ProductSections.tensorProductSection s t) e'.hom).mp hqiso
  exact (SectionFrames.tensorProductSection_isIso_iff L M s t).mp hprod

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.InverseSectionFrames
