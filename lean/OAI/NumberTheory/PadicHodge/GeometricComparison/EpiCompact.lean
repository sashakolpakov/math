import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.ExtensionCompactCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleIs

/-! # Epi Compact -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.EpiCompact.EpiCompactLift

noncomputable section

/-! Local lifts of a morphism from the integer constant sheaf on a single affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} [CompactSpace X]
  {F G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}

theorem exists_lift (f : F ⟶ G) [Epi f] (a : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X ⟶ G) :
    ∃ (U : X.ProEt) (g : U ⟶ ⊤_ X.ProEt), IsAffine U.left ∧ Surjective g.left ∧
      ∃ s : F.obj.obj (op U),
        f.hom.app (op U) s = a.hom.app (op U) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))
    (inferInstanceAs (Mono (kernel.ι f))) inferInstance
  let T := AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction.pullbackExtensionComplex S a
  let E : Cohomology.ExtensionOf.CohomologyExtension.Extension X (kernel f) :=
    ⟨T.X₂, T.f, T.g, T.zero, AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions.Construction.pullbackExtensionComplex_shortExact hS a⟩
  obtain ⟨U, g, hU, hg, ⟨s⟩⟩ := E.exists_compact_cover_lift (⊤_ X.ProEt)
  refine ⟨U, g, hU, hg, (pullback.fst f a).hom.app (op U) s.val, ?_⟩
  have h := congrArg (fun k : pullback f a ⟶ G => k.hom.app (op U) s.val)
    (pullback.condition (f := f) (g := a))
  change f.hom.app (op U) ((pullback.fst f a).hom.app (op U) s.val) =
    a.hom.app (op U) (E.projection.hom.app (op U) s.val) at h
  rw [s.property] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.EpiCompact.EpiCompactLift
