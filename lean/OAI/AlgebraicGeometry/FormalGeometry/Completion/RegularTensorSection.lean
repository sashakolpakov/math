import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.TensorSectionMono
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleMonoCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularSectionCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent

/-! # Regular Tensor Section -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularTensorSection

noncomputable section

/-! A generated line bundle has a section regular on any specified coherent module,
when the global functions form an infinite field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

theorem exists_regular_tensor_section
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [Infinite Γ(X, ⊤)]
    (hfield : IsField Γ(X, ⊤)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf, Mono (TensorSectionMap.Construction.tensorSectionMap s M) := by
  obtain ⟨k, U, hU, e, hcover⟩ := L.exists_finite_affine_frames
  let V (i : Fin k) : X.affineOpens := ⟨U i, hU i⟩
  let d i := L.overFrameIso (U i) (e i).some
  obtain ⟨s, hs⟩ := RegularSectionCoefficients.Construction.exists_global_section_regular_on_affine_frames hfield L.sheaf hL M V d
  let a := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm s
  have hq : (M ⊗ L.sheaf).IsQuasicoherent :=
    (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L).tensorObj_isQuasicoherent
  have : (L.sheaf ⊗ M).IsQuasicoherent :=
    (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent X).prop_of_iso (β_ M L.sheaf) hq
  refine ⟨a, ModuleMonoCover.Construction.moduleMap_mono_of_locally_restrict _ (fun x => ?_)⟩
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨U i, hi, Affine.TensorSectionMono.Construction.tensorSectionMap_restrict_mono_of_regular_coefficient a M (V i) (d i) ?_⟩
  simpa only [a, Equiv.apply_symm_apply] using hs i

theorem exists_mono_tensor_generated_lineBundle
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] [Infinite Γ(X, ⊤)]
    (hfield : IsField Γ(X, ⊤)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : Frame.SectionDetection.Construction.HasFrameSections L.sheaf)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ a : M ⟶ M ⊗ L.sheaf, Mono a := by
  obtain ⟨s, hs⟩ := exists_regular_tensor_section hfield L hL M
  have := hs
  exact ⟨TensorSectionMap.Construction.tensorSectionMap s M ≫ (β_ L.sheaf M).hom, inferInstance⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularTensorSection
