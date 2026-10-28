import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ParameterRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerParameterRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPolarizationGraphRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.MorphismSheaf

/-! # Dual Graph Power Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Positive graph powers make the local polarization maps into a
compatible family on the fixed actual dual. Their underlying maps then
glue on all test schemes by the existing family-morphism sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (D : Dual.Data.DualAbelianData A)
  (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ) {δ : Fin g → ℕ}

def Line.Bundles.LineBundle.parameterSinglePullbackIso {U T : Over S} (c : U ⟶ T) :
    ((L.pullback (pullback.fst A.scheme.hom T.hom)).pullback
      (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)).sheaf ≅
      (L.pullback (pullback.fst A.scheme.hom U.hom)).sheaf :=
  (Scheme.Modules.pullbackComp (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)
    (pullback.fst A.scheme.hom T.hom)).app L.sheaf ≪≫
  (Scheme.Modules.pullbackCongr (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A.scheme)).app L.sheaf

theorem Fixed.DualGraphPowerGluing.fixedDualGraphPower_parameterPullback {U T : Over S} (c : U ⟶ T)
    (p : PolarizationData.Polarization (D.pullback T.hom) δ)
    (hp : Nonempty ((L.pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.isogeny.hom).tensorPower d).sheaf)) :
    Nonempty ((L.pullback (pullback.fst A.scheme.hom U.hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom)
        (Polarization.ParameterRestriction.polarizationParameterPullback A D c p).isogeny.hom).tensorPower d).sheaf) := by
  rw [Polarization.ParameterRestriction.polarizationParameterPullback_hom]
  exact ⟨(L.parameterSinglePullbackIso A c).symm ≪≫
    (Scheme.Modules.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)).mapIso hp.some ≪≫
      Affine.GraphPowerParameterRestriction.AffineRawGraphPower.parameterGraphPowerIso A D c p.isogeny.hom d⟩

variable [IsNoetherian S] (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
  (level : A.FullLevel N) (hd : 0 < d) (hδ : ∀ i, 0 < δ i)

include P level hd hδ in
theorem Fixed.DualGraphPowerGluing.fixedDualGraphPower_hom_unique (T : Over S)
    (p q : PolarizationData.Polarization (D.pullback T.hom) δ)
    (hp : Nonempty ((L.pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.isogeny.hom).tensorPower d).sheaf))
    (hq : Nonempty ((L.pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) q.isogeny.hom).tensorPower d).sheaf)) :
    p.isogeny.hom = q.isogeny.hom := by
  apply Universal.TestPolarizationGraphRecovery.universalTest_polarization_hom_eq_of_graphPower A P T (D.pullback T.hom)
    p q (level.pullback T.hom) hδ d hd
  have h : Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.isogeny.hom).tensorPower d) =
      Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) q.isogeny.hom).tensorPower d) :=
    Quotient.sound ⟨hp.some.symm ≪≫ hq.some⟩
  simpa only [Line.Bundles.LineBundle.classOf_tensorPower] using h

include P level hd hδ in
theorem Fixed.DualGraphPowerGluing.fixedDualGraphPower_restriction_unique {U T : Over S} (c : U ⟶ T)
    (p : PolarizationData.Polarization (D.pullback T.hom) δ) (q : PolarizationData.Polarization (D.pullback U.hom) δ)
    (hp : Nonempty ((L.pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.isogeny.hom).tensorPower d).sheaf))
    (hq : Nonempty ((L.pullback (pullback.fst A.scheme.hom U.hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom) q.isogeny.hom).tensorPower d).sheaf)) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p.isogeny.hom = q.isogeny.hom :=
  (Polarization.ParameterRestriction.polarizationParameterPullback_hom A D c p).symm.trans
    (Fixed.DualGraphPowerGluing.fixedDualGraphPower_hom_unique A D L d P level hd hδ U
      (Polarization.ParameterRestriction.polarizationParameterPullback A D c p) q
      (Fixed.DualGraphPowerGluing.fixedDualGraphPower_parameterPullback A D L d c p hp) hq)

include P level hd hδ in
theorem Fixed.DualGraphPowerGluing.fixedDualGraphPower_maps_glue
    (T : Over S) (R : Sieve T) (hR : R ∈ (Scheme.zariskiTopology.over S) T)
    (p : ∀ {U : Over S} (c : U ⟶ T), R c → PolarizationData.Polarization (D.pullback U.hom) δ)
    (hp : ∀ {U : Over S} (c : U ⟶ T) (hc : R c),
      Nonempty ((L.pullback (pullback.fst A.scheme.hom U.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom) (p c hc).isogeny.hom).tensorPower d).sheaf)) :
    ∃ f : (A.pullback T.hom).scheme ⟶ (D.pullback T.hom).abelian.scheme,
      ∀ {U : Over S} (c : U ⟶ T) (hc : R c),
        Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f = (p c hc).isogeny.hom := by
  let F := Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A.scheme D.abelian.scheme
  let s : Presieve.FamilyOfElements F R.arrows := fun {U} c hc => (p c hc).isogeny.hom
  have hs : s.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro U V c a hc
    exact (Fixed.DualGraphPowerGluing.fixedDualGraphPower_restriction_unique A D L d P level hd hδ a
      (p c hc) (p (a ≫ c) (R.downward_closed hc a)) (hp c hc)
      (hp (a ≫ c) (R.downward_closed hc a))).symm
  have hF := Family.MorphismSheaf.geometricFamilyMorphismFunctor_isSheaf_subcanonical
    A.scheme D.abelian.scheme Scheme.zariskiTopology
  obtain ⟨f, hf, _⟩ := (isSheaf_iff_isSheaf_of_type _ _).mp hF R hR s hs
  refine ⟨f, ?_⟩
  intro U c hc
  exact hf c hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
