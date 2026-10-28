import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.FppfSheafExistence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.BundleNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleNormalization

/-! # Bundle Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.BundleIsoDescent.Construction

noncomputable section

/-! Normalized bundle isomorphisms descend over a Noetherian test
scheme. The original family may have an arbitrary base; only the actual
test schemes used for the fppf gluing need to be Noetherian. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleNormalization

variable {X S : Scheme.{0}} (p : X ⟶ S)
  [IsProper p] [Smooth p] [GeometricallyConnected p]
  (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)

theorem noetherian_familyBaseChangeSection_bijective
    (T : Over S) [IsLocallyNoetherian T.left] :
    Function.Bijective ((AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection p σ hσ).app T).left.appTop := by
  have : IsIso ((AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection p σ hσ).app T).left.appTop :=
    BundleNormalization.Construction.noetherian_section_globalFunctions_isIso (Limits.pullback.fst T.hom p)
      ((AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection p σ hσ).app T).left (AbelianModuli.HilbertConstruction.Section.BaseChangeFunctor.familyBaseChangeSection_fst p σ hσ T)
  exact ConcreteCategory.bijective_of_isIso _

variable (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
  (b : (Scheme.Modules.pullback σ).obj L.sheaf ≅ (Scheme.Modules.pullback σ).obj M.sheaf)

theorem noetherian_normalizedBundleIso_nonempty_of_cover
    (T : Over S) [IsLocallyNoetherian T.left]
    (R : Sieve T) (hR : R ∈ (Scheme.fppfTopology.over S) T)
    (hlocal : ∀ (U : Over S) [IsLocallyNoetherian U.left] (f : U ⟶ T), R f →
      Nonempty ((AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (op U))) :
    Nonempty ((AbelianModuli.HilbertConstruction.Normalized.BundleIsoSheaf.normalizedBundleIsoPresheaf p σ hσ L M b).obj (op T)) := by
  refine FppfSheafExistence.Construction.noetherian_fppf_sheaf_nonempty_of_cover _
    (AbelianModuli.HilbertConstruction.Normalized.BundleIsoSheaf.normalizedBundleIsoPresheaf_isSheaf_subcanonical p σ hσ L M b Scheme.fppfTopology)
    ?_ T R hR ?_
  · intro U _
    exact AbelianModuli.HilbertConstruction.Relative.BundleNormalization.normalizedBundleIsoPresheaf_subsingleton p σ hσ L M U b
      (noetherian_familyBaseChangeSection_bijective p σ hσ U).1
  · intro U _ f hf
    exact (AbelianModuli.HilbertConstruction.Relative.BundleNormalization.normalizedBundleIsoPresheaf_nonempty_iff p σ hσ L M U b
      (noetherian_familyBaseChangeSection_bijective p σ hσ U)).mpr (hlocal U f hf)

include b hσ in
theorem noetherian_relativeBundleIso_nonempty_of_cover
    (T : Over S) [IsLocallyNoetherian T.left]
    (R : Sieve T) (hR : R ∈ (Scheme.fppfTopology.over S) T)
    (hlocal : ∀ (U : Over S) [IsLocallyNoetherian U.left] (f : U ⟶ T), R f →
      Nonempty ((AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (op U))) :
    Nonempty ((AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (op T)) := by
  obtain ⟨e⟩ := noetherian_normalizedBundleIso_nonempty_of_cover p σ hσ L M b T R hR hlocal
  exact ⟨e.val⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.BundleIsoDescent.Construction
