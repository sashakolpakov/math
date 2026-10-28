import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerCompatibilityParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ParameterPullbackCoherence

/-! # Graph Power Parameter Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerParameterRestriction.AffineRawGraphPower

noncomputable section

/-! The raw graph-power parameter has its original-family meaning after
every parameter restriction. All comparisons use the native Cartesian
family maps, including on nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (D : Dual.Data.DualAbelianData A)

private theorem graphPullbackMap_fst {V : Scheme.{u}} (b : V ⟶ S)
    (p : (A.pullback b).scheme ⟶ (D.pullback b).abelian.scheme) :
    ((PoincareGraph.Bundles.poincareGraphMap (D.pullback b) p).left ≫
      (D.poincarePullbackOverMap b).left) ≫
        pullback.fst D.abelian.scheme.hom A.scheme.hom =
      p.left ≫ pullback.fst D.abelian.scheme.hom b :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (PoincareGraph.Bundles.poincareGraphMap (D.pullback b) p).left ≫ z)
      (D.poincarePullbackOverMap_left_fst b)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ pullback.fst D.abelian.scheme.hom b)
          (PoincareGraph.Bundles.poincareGraphMap_fst (D.pullback b) p))))

private theorem graphPullbackMap_snd {V : Scheme.{u}} (b : V ⟶ S)
    (p : (A.pullback b).scheme ⟶ (D.pullback b).abelian.scheme) :
    ((PoincareGraph.Bundles.poincareGraphMap (D.pullback b) p).left ≫
      (D.poincarePullbackOverMap b).left) ≫
        pullback.snd D.abelian.scheme.hom A.scheme.hom =
      pullback.fst A.scheme.hom b :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (PoincareGraph.Bundles.poincareGraphMap (D.pullback b) p).left ≫ z)
      (D.poincarePullbackOverMap_left_snd b)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ pullback.fst A.scheme.hom b)
          (PoincareGraph.Bundles.poincareGraphMap_snd (D.pullback b) p)).trans (Category.id_comp _))))

variable {U T : Over S} (c : U ⟶ T)
variable (p : (A.pullback T.hom).scheme ⟶ (D.pullback T.hom).abelian.scheme)

def parameterGraphBundleIso :
    (PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom) (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p).pullback
        (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)).sheaf := by
  let q := Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p
  let a := Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme
  let E := D.pullback T.hom
  let F := D.pullback U.hom
  let v := (PoincareGraph.Bundles.poincareGraphMap F q).left
  let w := (PoincareGraph.Bundles.poincareGraphMap E p).left
  let rU := (D.poincarePullbackOverMap U.hom).left
  let rT := (D.poincarePullbackOverMap T.hom).left
  have hq : q.left ≫ pullback.fst D.abelian.scheme.hom U.hom =
      a ≫ p.left ≫ pullback.fst D.abelian.scheme.hom T.hom := by
    calc
      q.left ≫ pullback.fst D.abelian.scheme.hom U.hom =
          q.left ≫ (Single.ParameterBaseChange.singleParameterBaseChangeMap c D.abelian.scheme ≫
            pullback.fst D.abelian.scheme.hom T.hom) :=
        congrArg (fun z => q.left ≫ z) (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c D.abelian.scheme).symm
      _ = (q.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c D.abelian.scheme) ≫
          pullback.fst D.abelian.scheme.hom T.hom := (Category.assoc _ _ _).symm
      _ = (a ≫ p.left) ≫ pullback.fst D.abelian.scheme.hom T.hom :=
        congrArg (fun z => z ≫ pullback.fst D.abelian.scheme.hom T.hom)
          (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange_comp c p)
      _ = _ := Category.assoc _ _ _
  have ha : a ≫ pullback.fst A.scheme.hom T.hom = pullback.fst A.scheme.hom U.hom :=
    Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A.scheme
  have he : v ≫ rU = a ≫ w ≫ rT := by
    apply Over.tensorObj_ext
    · have hv : (v ≫ rU) ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
          q.left ≫ pullback.fst D.abelian.scheme.hom U.hom :=
        graphPullbackMap_fst A D U.hom q
      have hw : (w ≫ rT) ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
          p.left ≫ pullback.fst D.abelian.scheme.hom T.hom :=
        graphPullbackMap_fst A D T.hom p
      exact hv.trans (hq.trans
        ((congrArg (fun z => a ≫ z) hw).symm.trans (Category.assoc _ _ _).symm))
    · have hv : (v ≫ rU) ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
          pullback.fst A.scheme.hom U.hom :=
        graphPullbackMap_snd A D U.hom q
      have hw : (w ≫ rT) ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
          pullback.fst A.scheme.hom T.hom :=
        graphPullbackMap_snd A D T.hom p
      exact hv.trans (ha.symm.trans
        ((congrArg (fun z => a ≫ z) hw).symm.trans (Category.assoc _ _ _).symm))
  exact (Scheme.Modules.pullbackComp v rU).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr he).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp a (w ≫ rT)).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback a).mapIso
      ((Scheme.Modules.pullbackComp w rT).symm.app D.poincare.sheaf)

def parameterGraphPowerIso (d : ℕ) :
    (((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p).tensorPower d).pullback
      (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)).sheaf ≅
    ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom)
      (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p)).tensorPower d).sheaf :=
  (PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p).powerBaseChangeIso
    (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme) d ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ d).mapIso (parameterGraphBundleIso A D c p).symm

def parameterNormalizedLineIso (L : Line.Bundles.LineBundle A.scheme.left) :
    (((A.pullback T.hom).zeroNormalizedBundle
      (L.pullback (pullback.fst A.scheme.hom T.hom))).pullback
        (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)).sheaf ≅
      ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom U.hom)).sheaf :=
  (Scheme.Modules.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)).mapIso
    (A.zeroNormalizedBundle_baseChangeIso L T.hom).symm ≪≫
    (Scheme.Modules.pullbackComp (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme)
      (pullback.fst A.scheme.hom T.hom)).app (A.zeroNormalizedBundle L).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A.scheme)).app
      (A.zeroNormalizedBundle L).sheaf

theorem parameter_hasPoint_iff_restriction
    [IsAffine T.left] [IsLocallyNoetherian T.left] [IsMonHom p]
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ) :
    Nonempty (Over.mk c.left ⟶ GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter (A.pullback T.hom) (D.pullback T.hom) p
      (P.baseChange T.hom) (L.pullback (pullback.fst A.scheme.hom T.hom)) d) ↔
      Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom U.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback U.hom)
          (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p)).tensorPower d).sheaf) := by
  have h := GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_cartesian_hasPoint_iff (A.pullback T.hom) (D.pullback T.hom) p
    (P.baseChange T.hom) (L.pullback (pullback.fst A.scheme.hom T.hom)) d
    (Single.ParameterBaseChange.singleParameterBaseChangeMap c A.scheme) (A.pullback U.hom).scheme.hom c.left
    (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback c A.scheme)
  constructor
  · intro hz
    exact ⟨(parameterNormalizedLineIso A c L).symm ≪≫ (h.mp hz).some ≪≫
      parameterGraphPowerIso A D c p d⟩
  · rintro ⟨e⟩
    exact h.mpr ⟨parameterNormalizedLineIso A c L ≪≫ e ≪≫
      (parameterGraphPowerIso A D c p d).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerParameterRestriction.AffineRawGraphPower
