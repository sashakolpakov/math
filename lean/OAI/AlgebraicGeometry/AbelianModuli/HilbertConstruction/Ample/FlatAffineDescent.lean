import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffinePowerSectionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismAmpleDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphismAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwiseGeneratingPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Flat Affine Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ampleness of a line bundle on a proper scheme over an affine base descends through a flat surjective affine base change, giving an actual projective presentation downstairs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y : Scheme.{u}} [IsAffine S] [IsAffine Y]
variable (f : X ⟶ S) [IsProper f] (g : Y ⟶ S) [Flat g] [Surjective g] (L : Line.Bundles.LineBundle X)

theorem Line.Bundles.LineBundle.isAmple_of_flat_affine_baseChange
    (hL : (L.pullback (pullback.fst f g)).IsAmple) : L.IsAmple := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hp : IsSeparated (f ≫ terminal.from S) := inferInstance
  have : IsSeparated (terminal.from X) := (terminal.comp_from f) ▸ hp
  have hsections := L.pointwise_power_sections_of_flat_affine_baseChange (IsPullback.of_hasPullback f g) hL
  obtain ⟨d, hd, n, s, hs⟩ := L.exists_generating_power_of_pointwise hsections
  have hpower : ((L.tensorPower d).pullback (pullback.fst f g)).IsAmple :=
    (hL.tensorPower d hd).of_iso (L.powerBaseChangeIso (pullback.fst f g) d).symm
  have : IsFinite (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) :=
    Section.MorphismAmpleDescent.sectionAbsoluteMorphism_isFinite_of_ample_surjective_baseChange f g (L.tensorPower d) s hs hpower
  exact ((L.tensorPower d).isAmple_of_affine_sectionMorphism f s hs).of_tensorPower d hd

theorem Line.Bundles.LineBundle.isAmple_iff_flat_affine_baseChange :
    L.IsAmple ↔ (L.pullback (pullback.fst f g)).IsAmple := by
  have : IsAffineHom (pullback.fst f g) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f g).flip (inferInstance : IsAffineHom g)
  exact ⟨fun h => h.pullback_of_isAffineHom _, L.isAmple_of_flat_affine_baseChange f g⟩

def Line.Bundles.LineBundle.projectivePresentation_of_flat_affine_baseChange
    (hL : (L.pullback (pullback.fst f g)).IsAmple) : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) :=
  (L.isAmple_of_flat_affine_baseChange f g hL).projectivePresentation f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
