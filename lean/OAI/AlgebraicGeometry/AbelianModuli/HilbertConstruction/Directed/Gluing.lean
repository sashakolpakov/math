import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.OpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.IsoOperations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.SchemeTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverIsoNaturality
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.Gluing

noncomputable section

/-! Effective gluing of actual abelian schemes on a locally directed
open cover. The data are the original Cartesian transition maps, their
literal composition laws, and preservation of the group law. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

local instance nativePullbackGroup {S T : Scheme.{u}} (X : Over S) [GrpObj X] (f : T ⟶ S) :
    GrpObj ((Over.pullback f).obj X) := Functor.grpObjObj

structure DirectedAbelianGluingData {S : Scheme.{u}} (C : S.OpenCover.{u})
    [Category C.I₀] [C.LocallyDirected] (g : ℕ) where
  family : ∀ i, Abelian.Schemes.AbelianScheme g (C.X i)
  transition : ∀ {i j : C.I₀} (_ : i ⟶ j), (family i).scheme.left ⟶ (family j).scheme.left
  transition_id : ∀ i, transition (𝟙 i) = 𝟙 (family i).scheme.left
  transition_comp : ∀ {i j k : C.I₀} (f : i ⟶ j) (h : j ⟶ k),
    transition (f ≫ h) = transition f ≫ transition h
  cartesian : ∀ {i j : C.I₀} (f : i ⟶ j),
    IsPullback (transition f) (family i).scheme.hom (family j).scheme.hom (C.trans f)
  group : ∀ {i j : C.I₀} (f : i ⟶ j),
    IsMonHom (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (transition f) (C.trans f) (cartesian f)).hom

namespace DirectedAbelianGluingData
variable {S : Scheme.{u}} {C : S.OpenCover.{u}}
  [Category C.I₀] [C.LocallyDirected] [Small.{u} C.I₀] [Quiver.IsThin C.I₀]
  {g : ℕ} (D : DirectedAbelianGluingData C g)

def diagram : C.I₀ ⥤ Scheme.{u} where
  obj i := (D.family i).scheme.left
  map f := D.transition f
  map_id := D.transition_id
  map_comp := D.transition_comp

def schemeData : C.RelativeGluingData where
  functor := D.diagram
  natTrans :=
    { app i := (D.family i).scheme.hom
      naturality _ _ f := (D.cartesian f).w }
  equifibered _ _ f := D.cartesian f

/-- The total scheme is the genuine colimit of the original local total schemes. -/
def space : Over S := Over.mk D.schemeData.toBase

def chartMap (i : C.I₀) : (D.family i).scheme.left ⟶ D.space.left :=
  colimit.ι D.schemeData.functor i

instance chartMap_open (i : C.I₀) : IsOpenImmersion (D.chartMap i) := by
  exact D.schemeData.cover.map_prop i

theorem chartMap_over (i : C.I₀) :
    D.chartMap i ≫ D.space.hom = (D.family i).scheme.hom ≫ C.f i :=
  D.schemeData.ι_toBase i

theorem chartMap_transition {i j : C.I₀} (f : i ⟶ j) :
    D.transition f ≫ D.chartMap j = D.chartMap i :=
  colimit.w D.schemeData.functor f

theorem chart_cartesian (i : C.I₀) :
    IsPullback (D.chartMap i) (D.family i).scheme.hom D.space.hom (C.f i) :=
  (D.schemeData.isPullback_natTrans_ι_toBase i).flip

def chartIso (i : C.I₀) :
    (D.family i).scheme ≅ (Over.pullback (C.f i)).obj D.space :=
  ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (D.chartMap i) (C.f i) (D.chart_cartesian i)

theorem chartIso_fst (i : C.I₀) :
    (D.chartIso i).hom.left ≫ pullback.fst D.space.hom (C.f i) = D.chartMap i :=
  (D.chart_cartesian i).isoPullback_hom_fst

def transitionIso {i j : C.I₀} (f : i ⟶ j) :
    (D.family i).scheme ≅ (Over.pullback (C.trans f)).obj (D.family j).scheme :=
  ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (D.transition f) (C.trans f) (D.cartesian f)

instance transitionIso_group {i j : C.I₀} (f : i ⟶ j) : IsMonHom (D.transitionIso f).hom :=
  D.group f

private theorem chartIso_natural_left {i j : C.I₀} (f : i ⟶ j) :
    D.transition f ≫ (D.chartIso j).hom.left =
      (D.chartIso i).hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space := by
  let : Mono (pullback.fst D.space.hom (C.f j)) := inferInstance
  have hp : Single.ParameterBaseChange.singleParameterBaseChangeMap (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space ≫
      pullback.fst D.space.hom (C.f j) = pullback.fst D.space.hom (C.f i) :=
    Single.ParameterBaseChange.singleParameterBaseChangeMap_comp (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space
  apply (cancel_mono (pullback.fst D.space.hom (C.f j))).mp
  rw [Category.assoc, D.chartIso_fst, D.chartMap_transition,
    Category.assoc, hp, D.chartIso_fst]

theorem chartIso_natural {i j : C.I₀} (f : i ⟶ j) :
    (D.transitionIso f).hom ≫ (Over.pullback (C.trans f)).map (D.chartIso j).hom =
      (D.chartIso i).hom ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).hom :=
  Cartesian.OverIsoNaturality.cartesianAmbientOverIso_natural (C.trans f) (D.transition f)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space)
    (D.cartesian f)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space)
    (D.chartIso i).hom (D.chartIso j).hom ((chartIso_natural_left D) f)

/-- These local groups lie on the literal native pullbacks of the glued scheme. -/
def localAbelian (i : C.I₀) : Abelian.Schemes.AbelianScheme g (C.X i) :=
  (D.family i).transport (D.chartIso i)

private theorem local_comparison_group {i j : C.I₀} (f : i ⟶ j) :
    letI : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C i).hom).obj D.space) :=
      (D.localAbelian i).group
    letI : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space) :=
      (D.localAbelian j).group
    letI : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f).left).obj
        ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space)) :=
      Functor.grpObjObj
    IsMonHom (Single.ParameterBaseChange.singleParameterBaseChangeIso
      (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).hom := by
  let : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C i).hom).obj D.space) :=
    (D.localAbelian i).group
  let : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space) :=
    (D.localAbelian j).group
  let : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f).left).obj
      ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space)) :=
    Functor.grpObjObj
  let ei : (D.family i).scheme ≅
      (Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C i).hom).obj D.space := D.chartIso i
  let ej : (D.family j).scheme ≅
      (Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space := D.chartIso j
  let et : (D.family i).scheme ≅
      (Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f).left).obj (D.family j).scheme :=
    D.transitionIso f
  let : IsMonHom ei.hom := isMonHom_ofIso ei
  let : IsMonHom ej.hom := isMonHom_ofIso ej
  let : IsMonHom et.hom := D.group f
  have hsq : et.hom ≫ (Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f).left).map ej.hom =
      ei.hom ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).hom :=
    D.chartIso_natural f
  have he : (Single.ParameterBaseChange.singleParameterBaseChangeIso
      (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).hom =
      ei.inv ≫ et.hom ≫ (Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f).left).map ej.hom := by
    rw [hsq, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

def localOperations (i : C.I₀) : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback (C.f i)).obj D.space) :=
  FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj (D.localAbelian i).scheme

theorem localOperations_laws (i : C.I₀) : (D.localOperations i).Laws :=
  FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj_laws (D.localAbelian i).scheme

theorem localOperations_natural {i j : C.I₀} (f : i ⟶ j) :
    (D.localOperations j).geometricBaseChange (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) =
      D.localOperations i := by
  let : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C i).hom).obj D.space) :=
    (D.localAbelian i).group
  let : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space) :=
    (D.localAbelian j).group
  let : GrpObj ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f).left).obj
      ((Over.pullback (FamilyHomGluing.DirectedFamilyHomGluing.test C j).hom).obj D.space)) :=
    Functor.grpObjObj
  let : IsMonHom (Single.ParameterBaseChange.singleParameterBaseChangeIso
      (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).hom := (local_comparison_group D) f
  let : IsMonHom (Single.ParameterBaseChange.singleParameterBaseChangeIso
      (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).symm.hom :=
    inferInstanceAs (IsMonHom (Single.ParameterBaseChange.singleParameterBaseChangeIso
      (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).inv)
  exact FamilyGroup.IsoOperations.FamilyGroupOperations.ofGrpObj_ofIso
    (Single.ParameterBaseChange.singleParameterBaseChangeIso (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) D.space).symm

@[instance_reducible] def globalGroup : GrpObj D.space :=
  FamilyGroup.Operations.FamilyGroupOperations.descendGroup C D.localOperations D.localOperations_natural
    D.localOperations_laws

theorem globalGroup_commutative :
    letI := D.globalGroup
    IsCommMonObj D.space :=
  FamilyGroup.Operations.FamilyGroupOperations.descendGroup_commutative C D.localOperations D.localOperations_natural
    D.localOperations_laws

theorem globalGroup_pullback (i : C.I₀) :
    letI := D.globalGroup
    Functor.grpObjObj (F := Over.pullback (C.f i)) (G := D.space) = (D.localAbelian i).group := by
  let := D.globalGroup
  ext
  exact congrArg Over.Hom.left (congrArg FamilyGroup.Operations.FamilyGroupOperations.mul
    (FamilyGroup.Operations.FamilyGroupOperations.descend_baseChange C D.localOperations D.localOperations_natural i))

theorem localProperty (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ i, Q (D.family i).scheme.hom) : Q D.space.hom := by
  apply IsZariskiLocalAtTarget.of_openCover C
  intro i
  let e : Arrow.mk (D.family i).scheme.hom ≅
      Arrow.mk (pullback.snd D.space.hom (C.f i)) :=
    Arrow.isoMk ((Over.forget (C.X i)).mapIso (D.chartIso i)) (Iso.refl _) (by
      exact (D.chartIso i).hom.w.trans (Category.comp_id _).symm)
  exact (Q.arrow_mk_iso_iff e).mp (hQ i)

/-- The glued group is proper, smooth of relative dimension `g`, and
geometrically connected, because these properties hold on each chart. -/
def abelian : Abelian.Schemes.AbelianScheme g S where
  scheme := D.space
  group := D.globalGroup
  commutative := D.globalGroup_commutative
  proper := D.localProperty (@IsProper) (fun i => (D.family i).proper)
  smoothDimension := by
    let : IsZariskiLocalAtTarget
        (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget
        (P := @SmoothOfRelativeDimension g)
        (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g))
    exact D.localProperty (@SmoothOfRelativeDimension g) (fun i => (D.family i).smoothDimension)
  connected := by
    let : IsZariskiLocalAtTarget
        (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
      rw [GeometricallyConnected.eq_geometrically]
      infer_instance
    exact D.localProperty (@GeometricallyConnected) (fun i => (D.family i).connected)

instance chartIso_preservesGroup (i : C.I₀) :
    IsMonHom (show (D.family i).scheme ⟶ (D.abelian.pullback (C.f i)).scheme
      from (D.chartIso i).hom) := by
  let : GrpObj D.space := D.globalGroup
  change @IsMonHom (Over (C.X i)) _ _ (D.family i).scheme
    ((Over.pullback (C.f i)).obj D.space) (D.family i).group.toMonObj
    (Functor.grpObjObj (F := Over.pullback (C.f i)) (G := D.space)).toMonObj (D.chartIso i).hom
  rw [D.globalGroup_pullback i]
  exact isMonHom_ofIso (D.chartIso i)

end DirectedAbelianGluingData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.Gluing
