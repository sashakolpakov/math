import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AnnihilatorSubobjects
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.AdjunctionUnit

/-! # Closed Image Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.ClosedImageSupport

noncomputable section

/-! A closed direct image is supported on the actual closed image of
the source support. Proper source supports give strictly smaller images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def closedImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (Z : Closeds X) : Closeds Y :=
  ⟨f '' (Z : Set X), (IsClosedImmersion.isClosedEmbedding f).isClosedMap _ Z.isClosed⟩

theorem coherent_pushforward_support_le_closedImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (N : X.Modules) [N.IsQuasicoherent] [N.IsFiniteType] :
    letI := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f N
    letI := Finite.ImageType.finite_directImage_finiteType f N
    (Annihilator.coherentAnnihilator ((pushforward f).obj N)).support ≤
      closedImage f (Annihilator.coherentAnnihilator N).support := by
  let := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f N
  let := Finite.ImageType.finite_directImage_finiteType f N
  let Z := closedImage f (Annihilator.coherentAnnihilator N).support
  let U : Y.Opens := Z.compl
  apply (SupportSplitting.coherent_support_le_iff_restrict_compl_isZero _ Z).mpr
  have hN : Limits.IsZero (N.restrict (f ⁻¹ᵁ U).ι) := by
    apply (Module.VanishingOpen.module_restrict_isZero_iff_le_vanishingOpen N _).mpr
    intro x hx
    by_contra hn
    exact hx ⟨x, (Annihilator.coherentAnnihilator_mem_support_iff N x).mpr hn, rfl⟩
  have := OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap_isIso f U
  exact (asIso ((OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app N)).isZero_iff.mpr
    ((pushforward (f ∣_ U)).map_isZero hN)

theorem closedImage_lt_range_of_lt_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (Z : Closeds X) (hZ : Z < ⊤) : closedImage f Z < closedImage f ⊤ := by
  refine lt_of_le_of_ne (Set.image_mono le_top) ?_
  intro heq
  apply ne_of_lt hZ
  apply SetLike.coe_injective
  exact Set.image_injective.mpr (IsClosedImmersion.isClosedEmbedding f).injective
    (congrArg (fun W : Closeds Y => (W : Set Y)) heq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.ClosedImageSupport
