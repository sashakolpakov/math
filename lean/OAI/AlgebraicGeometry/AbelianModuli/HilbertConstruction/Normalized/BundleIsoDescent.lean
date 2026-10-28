import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubsingletonSheafExistence

/-! # Bundle Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent

noncomputable section

/-! Local unnormalized isomorphisms descend after imposing a unique normalization along a section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
variable (L M : Line.Bundles.LineBundle X)
variable (b : (Scheme.Modules.pullback x).obj L.sheaf ≅ (Scheme.Modules.pullback x).obj M.sheaf)

theorem normalizedBundleIso_nonempty_of_cover (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hΓ : ∀ T : Over S, Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left.appTop)
    (T : Over S) (R : Sieve T) (hR : R ∈ (J.over S) T)
    (hlocal : ∀ {U : Over S} (f : U ⟶ T), R f →
      Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op U))) :
    Nonempty ((BundleIsoSheaf.normalizedBundleIsoPresheaf p x hx L M b).obj (.op T)) := by
  refine SubsingletonSheafExistence.subsingletonSheaf_nonempty_of_cover (J.over S) _
    (BundleIsoSheaf.normalizedBundleIsoPresheaf_isSheaf_subcanonical p x hx L M b J) ?_ R hR ?_
  · intro U
    exact Relative.BundleNormalization.normalizedBundleIsoPresheaf_subsingleton p x hx L M U.unop b (hΓ U.unop).1
  · intro U f hf
    exact (Relative.BundleNormalization.normalizedBundleIsoPresheaf_nonempty_iff p x hx L M U b (hΓ U)).mpr (hlocal f hf)

include b in
theorem relativeBundleIso_nonempty_of_cover (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hΓ : ∀ T : Over S, Function.Bijective ((Section.BaseChangeFunctor.familyBaseChangeSection p x hx).app T).left.appTop)
    (T : Over S) (R : Sieve T) (hR : R ∈ (J.over S) T)
    (hlocal : ∀ {U : Over S} (f : U ⟶ T), R f →
      Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op U))) :
    Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op T)) := by
  obtain ⟨e⟩ := normalizedBundleIso_nonempty_of_cover p x hx L M b J hΓ T R hR hlocal
  exact ⟨e.val⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent
