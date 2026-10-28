import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentSupportSplit
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorSubobjects

/-! # Coherent Closed Image Support -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentClosedImageSupport

noncomputable section

/-! A closed direct image is supported on the actual closed image of
the source support. Proper source supports give strictly smaller images. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def closedImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (Z : Closeds X) : Closeds Y :=
  ⟨f '' (Z : Set X), (IsClosedImmersion.isClosedEmbedding f).isClosedMap _ Z.isClosed⟩

theorem coherent_pushforward_support_le_closedImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (N : X.Modules) [N.IsQuasicoherent] [N.IsFiniteType] :
    letI := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (M := N) f
    letI := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion (M := N) f
    (CoherentAnnihilator.coherentAnnihilator ((pushforward f).obj N)).support ≤
      closedImage f (CoherentAnnihilator.coherentAnnihilator N).support := by
  let := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (M := N) f
  let := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion (M := N) f
  let Z := closedImage f (CoherentAnnihilator.coherentAnnihilator N).support
  let U : Y.Opens := Z.compl
  apply (CoherentSupportSplit.coherent_support_le_iff_restrict_compl_isZero _ Z).mpr
  have hN : Limits.IsZero (N.restrict (f ⁻¹ᵁ U).ι) := by
    apply (ModuleVanishingOpen.module_restrict_isZero_iff_le_vanishingOpen N _).mpr
    intro x hx
    by_contra hn
    exact hx ⟨x, (CoherentAnnihilator.coherentAnnihilator_mem_support_iff N x).mpr hn, rfl⟩
  exact (Quotients.FiniteDescent.OpenModule.Construction.OpenModuleBaseChange.moduleOpenBaseChangeIso f U N).isZero_iff.mpr
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

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentClosedImageSupport
