import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.OpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ZariskiOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.CanonicalDualTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange

/-! # Dual Graph Power Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerDescent

noncomputable section

/-! Genuine Zariski descent of normalized graph-power enhancements on
every test of a fixed Noetherian projective abelian family. An actual
global dual and a covering isogeny suffice; local dual choices disappear
through the canonical dual comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}

theorem fixedDualZeroNormalizedGraphPower_of_cover
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (D : Dual.Data.DualAbelianData A)
    (level : A.FullLevel N) (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ) (hd : 0 < d)
    (hδ : ∀ i, 0 < δ i) (T : Over S) (R : Sieve T)
    (hR : R ∈ (Scheme.zariskiTopology.over S) T)
    (p : ∀ {U : Over S} (c : U ⟶ T), R c → PolarizationData.Polarization (D.pullback U.hom) δ)
    (hp : ∀ {U : Over S} (c : U ⟶ T) (hc : R c),
      Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom U.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom) (p c hc).isogeny.hom).tensorPower d).sheaf)) :
    Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N S).pullback T.hom)
      ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)) d) := by
  obtain ⟨f, hf⟩ := DualGraphPowerGluing.fixedDualGraphPower_maps_glue A D (A.zeroNormalizedBundle L) d
    P level hd hδ T R hR p hp
  let I := Relative.ZariskiOpenCover.relativeZariskiOpenIndex T R
  let C : T.left.OpenCover.{u} := Scheme.Cover.mkOfCovers I
    (fun i => i.val.toScheme) (fun i => i.val.ι) (by
      intro x
      obtain ⟨i, hi⟩ := Relative.ZariskiOpenCover.relativeZariskiOpenIndex_covers T R hR x
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  let c : ∀ i : I, Relative.OpenModuleMaps.relativeOpen T i.val ⟶ T := fun i => Relative.OpenModuleMaps.relativeOpenInclusion T i.val
  let q : ∀ i : I, PolarizationData.Polarization ((D.pullback T.hom).pullback (C.f i)) δ :=
    fun i => Polarization.ParameterRecovery.polarizationParameterToIterated A D (c i) (p (c i) i.property)
  have hq (i : I) : (Over.pullback (C.f i)).map f = (q i).isogeny.hom :=
    (Polarization.ParameterRecovery.polarizationParameterToIterated_hom_eq A D (c i) (p (c i) i.property) f
      (hf (c i) i.property).symm).symm
  let pol := Polarization.OpenDescent.polarizationOfOpenCover (D.pullback T.hom) δ f C q hq
  have hpol : pol.isogeny.hom = f :=
    Polarization.OpenDescent.polarizationOfOpenCover_hom (D.pullback T.hom) δ f C q hq
  refine ⟨⟨D.pullback T.hom, pol, ?_⟩⟩
  apply Normalized.GraphPowerOpenCover.zeroNormalizedGraphPowerIso_of_openCover A P T.hom (level.pullback T.hom)
    (D.pullback T.hom) pol L d C
  intro i
  let M := (A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)
  let G := (PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) pol.isogeny.hom).tensorPower d
  have hi : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (c i) pol.isogeny.hom =
      (p (c i) i.property).isogeny.hom :=
    (congrArg (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (c i)) hpol).trans (hf (c i) i.property)
  have hline : Nonempty
      (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom (Relative.OpenModuleMaps.relativeOpen T i.val).hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback (Relative.OpenModuleMaps.relativeOpen T i.val).hom)
          (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (c i) pol.isogeny.hom)).tensorPower d).sheaf) := by
    rw [hi]
    exact hp (c i) i.property
  have hsingle : Nonempty
      ((M.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap (c i) A.scheme)).sheaf ≅
        (G.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap (c i) A.scheme)).sheaf) :=
    ⟨Line.Bundles.LineBundle.parameterSinglePullbackIso A (A.zeroNormalizedBundle L) (c i) ≪≫
      hline.some ≪≫
      (Affine.GraphPowerParameterRestriction.AffineRawGraphPower.parameterGraphPowerIso A D (c i) pol.isogeny.hom d).symm⟩
  exact Normalized.GraphPowerOpenCover.bundleIso_of_singleParameterPullback A.scheme (c i) M G hsingle

theorem zeroNormalizedGraphPowerEnhancement_of_cover
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (D : Dual.Data.DualAbelianData A)
    (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (level : A.FullLevel N)
    (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ) (hd : 0 < d) (hδ : ∀ i, 0 < δ i)
    (T : Over S) (R : Sieve T) (hR : R ∈ (Scheme.zariskiTopology.over S) T)
    (H : ∀ {U : Over S} (c : U ⟶ T), R c →
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N S).pullback U.hom)
        ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom U.hom)) d)) :
    Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      ((⟨A, level⟩ : Level.Data.AbelianSchemeWithFullLevel g N S).pullback T.hom)
      ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)) d) := by
  have h {U : Over S} (c : U ⟶ T) (hc : R c) :
      ∃ p : PolarizationData.Polarization (D.pullback U.hom) δ,
        Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom U.hom)).sheaf ≅
          ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom) p.isogeny.hom).tensorPower d).sheaf) := by
    let mb : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback U.hom) (D.pullback U.hom).abelian := m.pullback U.hom
    exact GraphPower.CanonicalDualTransport.graphPowerEnhancement_on_chosenDual A P U (D.pullback U.hom) mb
      (level.pullback U.hom) hδ _ d (H c hc).some
  let p : ∀ {U : Over S} (c : U ⟶ T), R c → PolarizationData.Polarization (D.pullback U.hom) δ :=
    fun c hc => Classical.choose (h c hc)
  exact fixedDualZeroNormalizedGraphPower_of_cover A P D level L d hd hδ T R hR p
    (fun c hc => Classical.choose_spec (h c hc))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DualGraphPowerDescent
