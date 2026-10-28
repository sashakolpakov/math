import OAI.AlgebraicGeometry.FormalGeometry.Completion.ModuleAffineEpi
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact

/-! # Pushforward Exact -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.PushforwardExact

noncomputable section

/-! Actual affine direct image preserves coherent epimorphisms and short exact sequences. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

theorem affineModulePushforward_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) [Epi a] : Epi ((Scheme.Modules.pushforward f).map a) := by
  have : (kernel a).IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel a
  let T := ShortComplex.mk (kernel.ι a) a (kernel.condition a)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.kernelSequence_exact a)
  apply ModuleAffineEpi.Construction.moduleMap_epi_of_affine_sections_surjective
  intro U
  exact SheafCohomology.Projective.AffineSectionExact.affineSections_surjective_of_shortExact hT (f ⁻¹ᵁ U.1) (U.2.preimage f)

theorem affineModulePushforward_shortExact {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (T.map (Scheme.Modules.pushforward f)).ShortExact := by
  have := hT.mono_f
  have := hT.epi_g
  have : Epi ((Scheme.Modules.pushforward f).map T.g) := affineModulePushforward_epi f T.g
  refine ShortComplex.ShortExact.mk'
    (hT.exact.map_of_mono_of_preservesKernel _ hT.mono_f inferInstance) ?_ ?_
  · change Mono ((Scheme.Modules.pushforward f).map T.f)
    infer_instance
  · change Epi ((Scheme.Modules.pushforward f).map T.g)
    infer_instance

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.PushforwardExact
