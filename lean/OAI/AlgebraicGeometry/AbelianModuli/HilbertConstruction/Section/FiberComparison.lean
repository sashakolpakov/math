import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleIsoSectionRestriction

/-! # Fiber Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FiberComparison

noncomputable section

/-! The natural restriction to a section agrees with pullback along the actual base-changed section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)

def moduleSectionFiberIso (T : Over S) (M : X.Modules) :
    (Scheme.Modules.pullback ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left).obj
        ((Scheme.Modules.pullback ((Over.pullback p).obj T).hom).obj M) ≅
      (Scheme.Modules.pullback T.hom).obj ((Scheme.Modules.pullback x).obj M) :=
  ((Scheme.Modules.pullbackComp ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left
      ((Over.pullback p).obj T).hom).app M ≪≫
    (Scheme.Modules.pullbackCongr ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T).w).app M) ≪≫
    (Scheme.Modules.pullbackComp T.hom x).symm.app M

def bundleSectionFiberEquiv (L M : Line.Bundles.LineBundle X) (T : Over S) :
    ((Scheme.Modules.pullback ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left).obj
        ((Scheme.Modules.pullback ((Over.pullback p).obj T).hom).obj L.sheaf) ≅
      (Scheme.Modules.pullback ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left).obj
        ((Scheme.Modules.pullback ((Over.pullback p).obj T).hom).obj M.sheaf)) ≃
      (Module.IsoPresheaf.moduleIsoPresheaf ((Scheme.Modules.pullback x).obj L.sheaf)
        ((Scheme.Modules.pullback x).obj M.sheaf)).obj (.op T) :=
  Iso.isoCongr (moduleSectionFiberIso p x hx T L.sheaf) (moduleSectionFiberIso p x hx T M.sheaf)

theorem bundleIsoRestrictionToSection_pullback (L M : Line.Bundles.LineBundle X) (T : Over S)
    (e : (Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op T)) :
    (BundleIsoSectionRestriction.bundleIsoRestrictionToSection p x hx L M).app (.op T) e =
      bundleSectionFiberEquiv p x hx L M T
        ((Scheme.Modules.pullback ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left).mapIso e) := by
  change (Scheme.Modules.pullback ((Over.pullback p).obj T).hom).obj L.sheaf ≅
    (Scheme.Modules.pullback ((Over.pullback p).obj T).hom).obj M.sheaf at e
  apply Iso.ext
  change Iso.homCongr ((Scheme.Modules.pullbackComp T.hom x).symm.app L.sheaf)
      ((Scheme.Modules.pullbackComp T.hom x).symm.app M.sheaf)
      (Module.MapSlicePullback.moduleMapPullbackAlong ((BaseChangeFunctor.familyBaseChangeSection p x hx).app T) e.hom) = _
  unfold Module.MapSlicePullback.moduleMapPullbackAlong Module.MapPullbackCongruence.moduleMapPullbackCongr Module.MapPullbackComposition.moduleMapPullbackComp
  rw [Module.MapPullbackComposition.moduleMap_homCongr_combine, Module.MapPullbackComposition.moduleMap_homCongr_combine]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FiberComparison
