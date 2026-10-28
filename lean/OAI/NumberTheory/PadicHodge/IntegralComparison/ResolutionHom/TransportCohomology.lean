import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.TransportEdges
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientQuasiIso

/-! # Transport Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.TransportCohomology

noncomputable section

/-! The balanced mixed-total comparison is natural for original Ext.
Only the two endpoint coefficient resolutions are injective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

private theorem through_edges {A : Type*} [Category A] {U V U' V' E E' : A}
    (e : U ≅ V) (e' : U' ≅ V') (m : V ⟶ V') (a : U ⟶ U')
    (h : U ⟶ E) (h' : U' ⟶ E') (f : E ⟶ E')
    (hm : e.hom ≫ m = a ≫ e'.hom) (ha : a ≫ h' = h ≫ f) :
    m ≫ (e'.inv ≫ h') = (e.inv ≫ h) ≫ f := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (m ≫ (e'.inv ≫ h')) = (e.hom ≫ m) ≫ (e'.inv ≫ h') :=
      (Category.assoc _ _ _).symm
    _ = (a ≫ e'.hom) ≫ (e'.inv ≫ h') := congrArg (fun b => b ≫ (e'.inv ≫ h')) hm
    _ = a ≫ h' := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = h ≫ f := ha
    _ = e.hom ≫ ((e.inv ≫ h) ≫ f) := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R]
  {Z Y : C} {W Y' : D} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
  (γ : (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
  (g : W ⟶ F.obj Z) (a : F.obj Y ⟶ Y')
  (hγ : F.map (I.ι.f 0) ≫ γ.f 0 = a ≫ J.ι.f 0)

def extMap (i : ℕ) : ModuleCat.of R (Ext.{z} Z Y i) ⟶ ModuleCat.of R (Ext.{z} W Y' i) :=
  IntegralComparison.Ext.ExactFunctorModule.component F R Z i Y ≫
    ModuleCat.ofHom ((Ext.mk₀ a).postcompOfLinear R (F.obj Z) (add_zero i)) ≫
      (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y' i).map g.op

include hγ in
theorem section_homology (i : ℕ) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F Z g γ) i ≫
      (InjectiveSectionCohomology.homologyIso R W J i).hom =
        (InjectiveSectionCohomology.homologyIso R Z I i).hom ≫ extMap F R g a i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  cases i with
  | zero =>
    exact AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.naturality R F Z g γ I.ι J.ι a hγ
      (fun b q => Ext.subsingleton_of_injective Z (I.cocomplex.X b) q)
      (fun b q => Ext.subsingleton_of_injective (F.obj Z) (J.cocomplex.X b) q)
      (fun b q => Ext.subsingleton_of_injective W (J.cocomplex.X b) q) 0 x
  | succ i =>
    exact AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.naturality R F Z g γ I.ι J.ι a hγ
      (fun b q => Ext.subsingleton_of_injective Z (I.cocomplex.X b) q)
      (fun b q => Ext.subsingleton_of_injective (F.obj Z) (J.cocomplex.X b) q)
      (fun b q => Ext.subsingleton_of_injective W (J.cocomplex.X b) q) (i + 1) x

variable (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)
  (ε : P ⟶ (ChainComplex.single₀ C).obj Z) (η : Q ⟶ (ChainComplex.single₀ D).obj W)
  [QuasiIso ε] [QuasiIso η] (hβ : β.f 0 ≫ F.map (ε.f 0) = η.f 0 ≫ g)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun A => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete A)

include hγ hβ in
theorem total_homology (i : ℕ) :
    HomologicalComplex.homologyMap (TransportEdges.totalMap F R P Q β γ) i ≫
      (Total.homologyIso R Q η J i).hom =
        (Total.homologyIso R P ε I i).hom ≫ extMap F R g a i := by
  let e := Total.edge R P ε I.cocomplex
  let e' := Total.edge R Q η J.cocomplex
  let m := TransportEdges.totalMap F R P Q β γ
  let s := AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F Z g γ
  let : QuasiIso e := Total.edge_quasiIso R P ε I.cocomplex I.injective
  let : QuasiIso e' := Total.edge_quasiIso R Q η J.cocomplex J.injective
  have hs : HomologicalComplex.homologyMap e i ≫ HomologicalComplex.homologyMap m i =
      HomologicalComplex.homologyMap s i ≫ HomologicalComplex.homologyMap e' i :=
    (HomologicalComplex.homologyMap_comp e m i).symm.trans
      ((congrArg (fun b => HomologicalComplex.homologyMap b i)
        (TransportEdges.source_edge F R P Q β γ ε η g hβ)).trans
          (HomologicalComplex.homologyMap_comp s e' i))
  exact through_edges (isoOfQuasiIsoAt e i) (isoOfQuasiIsoAt e' i)
    (HomologicalComplex.homologyMap m i) (HomologicalComplex.homologyMap s i)
    (InjectiveSectionCohomology.homologyIso R Z I i).hom
    (InjectiveSectionCohomology.homologyIso R W J i).hom (extMap F R g a i) hs
    (section_homology F R I J γ g a hγ i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.TransportCohomology
