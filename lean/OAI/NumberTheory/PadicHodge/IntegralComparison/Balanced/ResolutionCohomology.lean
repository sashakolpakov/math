import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.TransportCohomology

/-! # Resolution Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionCohomology

noncomputable section

/-! The actual source Čech cohomology computes original Ext by the two
mixed-resolution edges. This balanced comparison has direct geometric
naturality, independently of any source dimension-shift sign convention. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (P : ChainComplex C ℕ)
  {Z Y : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
  (I : InjectiveResolution Y) (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun A => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete A)

def homologyIso (i : ℕ) : (Acyclic.ChainCohomology.complex R Y P).homology i ≅
    ModuleCat.of R (Ext.{z} Z Y i) := by
  let e := ResolutionHom.CoefficientEdge.edge R P I.cocomplex I.ι
  let : QuasiIso e := ResolutionHom.CoefficientQuasiIso.edge_quasiIso R P I hP
  exact isoOfQuasiIsoAt e i ≪≫ ResolutionHom.Total.homologyIso R P ε I i

theorem homologyIso_hom (i : ℕ) : (homologyIso R P ε I hP i).hom =
    HomologicalComplex.homologyMap (ResolutionHom.CoefficientEdge.edge R P I.cocomplex I.ι) i ≫
      (ResolutionHom.Total.homologyIso R P ε I i).hom := rfl

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  [Linear R D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (Q : ChainComplex D ℕ) (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)
  {W Y' : D} (η : Q ⟶ (ChainComplex.single₀ D).obj W) [QuasiIso η]
  (J : InjectiveResolution Y')
  (hQ : ∀ a q, Subsingleton (Ext.{z} (Q.X a) Y' (q + 1)))
  (γ : (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
  (g : W ⟶ F.obj Z) (hβ : β.f 0 ≫ F.map (ε.f 0) = η.f 0 ≫ g)
  (a : F.obj Y ⟶ Y') (hγ : F.map (I.ι.f 0) ≫ γ.f 0 = a ≫ J.ι.f 0)

include hβ hγ in
theorem naturality (i : ℕ) :
    HomologicalComplex.homologyMap (ResolutionHom.TransportEdges.coefficientMap F R P Q β a) i ≫
      (homologyIso R Q η J hQ i).hom =
        (homologyIso R P ε I hP i).hom ≫ ResolutionHom.TransportCohomology.extMap F R g a i := by
  let c := ResolutionHom.TransportEdges.coefficientMap F R P Q β a
  let e := ResolutionHom.CoefficientEdge.edge R P I.cocomplex I.ι
  let e' := ResolutionHom.CoefficientEdge.edge R Q J.cocomplex J.ι
  let m := ResolutionHom.TransportEdges.totalMap F R P Q β γ
  have hc : HomologicalComplex.homologyMap e i ≫ HomologicalComplex.homologyMap m i =
      HomologicalComplex.homologyMap c i ≫ HomologicalComplex.homologyMap e' i :=
    (HomologicalComplex.homologyMap_comp e m i).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f i)
        (ResolutionHom.TransportEdges.coefficient_edge F R P Q β γ I.ι J.ι a hγ)).trans
          (HomologicalComplex.homologyMap_comp c e' i))
  rw [homologyIso_hom, homologyIso_hom, ← Category.assoc, ← hc, Category.assoc,
    ResolutionHom.TransportCohomology.total_homology F R I J γ g a hγ P Q β ε η hβ,
    ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionCohomology
