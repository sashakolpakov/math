import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundlePullbackNormalization

/-! # Rigidified Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedGlobalFunctions

noncomputable section

/-! Rigidified bundle isomorphisms along a map that identifies global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem rigidifiedBundleIso_subsingleton_of_globalFunctions (x : Y ⟶ X)
    (hx : Function.Injective x.appTop) (L M : RigidifiedLineBundles.RigidifiedLineBundle x) :
    Subsingleton (RigidifiedLineBundles.RigidifiedLineBundleIso L M) := by
  constructor
  intro e f
  apply RigidifiedLineBundles.RigidifiedLineBundleIso.ext
  exact Line.Bundles.LineBundle.iso_eq_of_globalFunctions x hx L.lineBundle M.lineBundle e.underlying f.underlying
    ((cancel_mono M.rigidification.hom).mp (e.normalized.trans f.normalized.symm))

theorem rigidifiedBundleIso_nonempty_iff_of_globalFunctions (x : Y ⟶ X)
    (hx : Function.Bijective x.appTop) (L M : RigidifiedLineBundles.RigidifiedLineBundle x) :
    Nonempty (RigidifiedLineBundles.RigidifiedLineBundleIso L M) ↔ Nonempty (L.lineBundle.sheaf ≅ M.lineBundle.sheaf) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.underlying⟩
  · intro h
    obtain ⟨a, ha, _⟩ := Line.Bundles.LineBundle.existsUnique_iso_with_pullback x hx L.lineBundle M.lineBundle h
      (L.rigidification ≪≫ M.rigidification.symm)
    refine ⟨⟨a, ?_⟩⟩
    have ha' : (Scheme.Modules.pullback x).map a.hom = L.rigidification.hom ≫ M.rigidification.inv := ha
    exact (congrArg (fun c => c ≫ M.rigidification.hom) ha').trans (by
      rw [Category.assoc, M.rigidification.inv_hom_id, Category.comp_id])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedGlobalFunctions
