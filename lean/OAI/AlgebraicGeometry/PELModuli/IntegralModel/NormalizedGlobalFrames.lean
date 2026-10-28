import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame

/-! # Normalized Global Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedGlobalFrames

noncomputable section

/-! A normalized isomorphism of globally framed lines preserves their
frames when the actual section detects line-bundle isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem normalizedIso_preserves_global_frames {X T : Scheme.{0}} (π : X ⟶ T) (z : T ⟶ X)
    (hz : z ≫ π = 𝟙 T) (hΓ : Function.Surjective π.appTop)
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (t : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (e : L.sheaf ≅ M.sheaf)
    (he : (Scheme.Modules.pullback z).mapIso e ≪≫
        ((Scheme.Modules.pullback z).mapIso t ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z) =
      (Scheme.Modules.pullback z).mapIso s ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z) :
    e ≪≫ t = s := by
  have hc : (Scheme.Modules.pullback z).map (s ≪≫ t.symm).hom ≫
      ((Scheme.Modules.pullback z).mapIso t ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z).hom =
        ((Scheme.Modules.pullback z).mapIso s ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z).hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.mapIso_hom,
      Category.assoc, Iso.map_inv_hom_id_assoc]
  have hu := Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.normalizedIso_unique π z hz hΓ L.locallyTrivial
    ((Scheme.Modules.pullback z).mapIso s ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z)
    ((Scheme.Modules.pullback z).mapIso t ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z)
    e (s ≪≫ t.symm) (congrArg CategoryTheory.Iso.hom he) hc
  rw [hu]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedGlobalFrames
