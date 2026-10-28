import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.IsoOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyMapLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PointedHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Recovery

/-! # Iso Covering Sieve Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Complete local isomorphisms over a Zariski covering sieve complete a common underlying family isomorphism globally. No group-law or dual-comparison premise is left on the global map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}

def Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_locallyNoetherian
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)
    (T : Over S) (R : Sieve T) (hR : R ∈ (Scheme.zariskiTopology.over S) T)
    (e : (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme)
    (a : ∀ {U : Over S} (c : U ⟶ T), R c →
      Moduli.Isomorphisms.LevelPreservingIso (A.pullback U.hom) (B.pullback U.hom))
    (ha : ∀ {U : Over S} (c : U ⟶ T) (hc : R c),
      (a c hc).abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c e.hom) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) := by
  have : IsMonHom e.hom := LocallyNoetherian.PointedHom.baseChangedPointedAbelianMap_isMonHom_of_locallyNoetherian A B T e.hom
    (PointedFamilyMapLocality.geometricFamilyMap_preserves_unit_of_cover A.abelian.scheme B.abelian.scheme
      Scheme.zariskiTopology T R hR e.hom (by
        intro U c hc
        rw [← ha c hc]
        exact IsMonHom.one_hom (a c hc).abelian.hom))
  let I := Relative.ZariskiOpenCover.relativeZariskiOpenIndex T R
  let C : Scheme.OpenCover T.left := Scheme.Cover.mkOfCovers I
    (fun i => i.val.toScheme) (fun i => i.val.ι) (by
      intro x
      obtain ⟨i, hi⟩ := Relative.ZariskiOpenCover.relativeZariskiOpenIndex_covers T R hR x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  let b := fun i : I => (Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv A B (Relative.OpenModuleMaps.relativeOpenInclusion T i.val)).symm
    (a (Relative.OpenModuleMaps.relativeOpenInclusion T i.val) i.property)
  exact Moduli.Isomorphisms.LevelPreservingIso.ofOpenCover_abelian_locallyNoetherian A B hδ T e C b (fun i =>
    Moduli.Isomorphisms.LevelPreservingIso.iteratedParameterPointEquiv_symm_abelian_hom A B (Relative.OpenModuleMaps.relativeOpenInclusion T i.val)
      (a (Relative.OpenModuleMaps.relativeOpenInclusion T i.val) i.property) e.hom
      (ha (Relative.OpenModuleMaps.relativeOpenInclusion T i.val) i.property))

theorem Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_locallyNoetherian_hom
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)
    (T : Over S) (R : Sieve T) (hR : R ∈ (Scheme.zariskiTopology.over S) T)
    (e : (A.pullback T.hom).abelian.scheme ≅ (B.pullback T.hom).abelian.scheme)
    (a : ∀ {U : Over S} (c : U ⟶ T), R c →
      Moduli.Isomorphisms.LevelPreservingIso (A.pullback U.hom) (B.pullback U.hom))
    (ha : ∀ {U : Over S} (c : U ⟶ T) (hc : R c),
      (a c hc).abelian.hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c e.hom) :
    (Moduli.Isomorphisms.LevelPreservingIso.ofCoveringSieve_abelian_locallyNoetherian A B hδ T R hR e a ha).abelian.hom = e.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
