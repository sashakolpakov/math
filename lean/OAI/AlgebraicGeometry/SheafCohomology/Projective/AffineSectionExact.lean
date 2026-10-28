import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections
import OAI.AlgebraicGeometry.SheafCohomology.Module

/-! # Affine Section Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact

noncomputable section

/-! Lifting sections of actual short exact sequences over affine opens. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

/-- A quasicoherent kernel makes sections of a short exact sequence surjective
over any affine open, by the proved vanishing of its first cohomology. -/
theorem affineSections_surjective_of_shortExact {X : Scheme.{u}}
    {T : ShortComplex X.Modules} (hT : T.ShortExact) [T.X₁.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) : Function.Surjective (T.g.app U) := by
  let F := Module.ProjectiveAffine.ModuleSheaf.toSheaf X
  have hF : (T.map F).ShortExact := hT.map_of_exact F
  let R := Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{u} U.isOpenEmbedding
  have : R.Additive := Cech.TopCatRestrict.TopCat.Sheaf.restrict_additive U.isOpenEmbedding
  have : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  have : PreservesFiniteLimits R := Cech.TopCatRestrict.TopCat.Sheaf.restrict_preservesFiniteLimits U.isOpenEmbedding
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let S := (T.map F).map R
  have hS : S.ShortExact := hF.map_of_exact R
  have : IsAffine U.toScheme := hU
  have : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
    change Subsingleton (AffineH.Projective.H ((Scheme.Modules.restrictFunctor U.ι).obj T.X₁) 1)
    exact AffineVanishing.Projective.moduleAffineHSucc_subsingleton _ 0
  have hsurj := Exact.CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
    hS (isTerminalTop : IsTerminal (⊤ : Opens (U.toScheme)))
  change Function.Surjective
    ((F.map T.g).hom.app (op (U.isOpenEmbedding.functor.obj ⊤))) at hsurj
  rw [Opens.isOpenEmbedding_obj_top U] at hsurj
  exact hsurj

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineSectionExact
