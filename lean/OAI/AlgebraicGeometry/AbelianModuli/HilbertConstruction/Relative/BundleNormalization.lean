import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundlePullbackNormalization

/-! # Bundle Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleNormalization

noncomputable section

/-! When a section identifies global functions, relative bundle isomorphisms admit unique normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
variable (L M : Line.Bundles.LineBundle X) (T : Over S)

theorem bundleIsoRestrictionToSection_injective
    (hf : Function.Injective ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left.appTop) :
    Function.Injective ((BundleIsoSectionRestriction.bundleIsoRestrictionToSection p x hx L M).app (.op T)) := by
  intro e d h
  have h' := (Section.FiberComparison.bundleSectionFiberEquiv p x hx L M T).injective
    ((Section.FiberComparison.bundleIsoRestrictionToSection_pullback p x hx L M T e).symm.trans
      (h.trans (Section.FiberComparison.bundleIsoRestrictionToSection_pullback p x hx L M T d)))
  exact Line.Bundles.LineBundle.iso_eq_of_globalFunctions _ hf
    (L.pullback ((Over.pullback p).obj T).hom) (M.pullback ((Over.pullback p).obj T).hom)
    e d (congrArg Iso.hom h')

theorem bundleIsoRestrictionToSection_surjective_of_nonempty
    (hf : Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left.appTop)
    (hLM : Nonempty ((BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op T))) :
    Function.Surjective ((BundleIsoSectionRestriction.bundleIsoRestrictionToSection p x hx L M).app (.op T)) := by
  intro c
  let c' := (Section.FiberComparison.bundleSectionFiberEquiv p x hx L M T).symm c
  obtain ⟨e, he, _⟩ := Line.Bundles.LineBundle.existsUnique_iso_with_pullback _ hf
    (L.pullback ((Over.pullback p).obj T).hom) (M.pullback ((Over.pullback p).obj T).hom) hLM c'
  have he' : (Scheme.Modules.pullback ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left).mapIso e = c' :=
    Iso.ext he
  refine ⟨e, (Section.FiberComparison.bundleIsoRestrictionToSection_pullback p x hx L M T e).trans ?_⟩
  exact (congrArg (Section.FiberComparison.bundleSectionFiberEquiv p x hx L M T) he').trans
    ((Section.FiberComparison.bundleSectionFiberEquiv p x hx L M T).apply_symm_apply c)

variable (b : (Scheme.Modules.pullback x).obj L.sheaf ≅ (Scheme.Modules.pullback x).obj M.sheaf)

theorem normalizedBundleIsoPresheaf_subsingleton
    (hf : Function.Injective ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left.appTop) :
    Subsingleton ((Normalized.BundleIsoSheaf.normalizedBundleIsoPresheaf p x hx L M b).obj (.op T)) := by
  constructor
  intro e d
  apply Subtype.ext
  exact bundleIsoRestrictionToSection_injective p x hx L M T hf (e.property.trans d.property.symm)

theorem normalizedBundleIsoPresheaf_nonempty_iff
    (hf : Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left.appTop) :
    Nonempty ((Normalized.BundleIsoSheaf.normalizedBundleIsoPresheaf p x hx L M b).obj (.op T)) ↔
      Nonempty ((BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op T)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.val⟩
  · intro h
    obtain ⟨e, he⟩ := bundleIsoRestrictionToSection_surjective_of_nonempty p x hx L M T hf h
      ((Scheme.Modules.pullback T.hom).mapIso b)
    exact ⟨⟨e, he⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleNormalization
