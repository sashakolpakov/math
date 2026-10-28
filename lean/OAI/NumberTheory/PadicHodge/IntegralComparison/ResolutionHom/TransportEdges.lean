import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Transport
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.CoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexCoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHorizontalEdge
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality

/-! # Transport Edges -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.TransportEdges

noncomputable section

/-! Both literal augmentation-edge squares for geometric transport of
the original mixed Hom total. These statements impose no injectivity
condition on the transported coefficient complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private theorem source_formula {U Z Y : C} {V W Y' : D}
    (e : U ⟶ Z) (b : V ⟶ F.obj U) (h : V ⟶ W) (g : W ⟶ F.obj Z)
    (c : F.obj Y ⟶ Y') (hb : b ≫ F.map e = h ≫ g) (x : Ext.{z} Z Y 0) :
    (Ext.mk₀ b).comp ((((Ext.mk₀ e).comp x (zero_add 0)).mapExactFunctor F).comp
        (Ext.mk₀ c) (add_zero 0)) (zero_add 0) =
      (Ext.mk₀ h).comp ((Ext.mk₀ g).comp
        ((x.mapExactFunctor F).comp (Ext.mk₀ c) (add_zero 0)) (zero_add 0)) (zero_add 0) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective Z Y).surjective x
  simp only [Ext.mk₀_comp_mk₀, Ext.mapExactFunctor_mk₀, F.map_comp]
  apply congrArg Ext.mk₀
  simp only [Category.assoc]
  rw [← Category.assoc b (F.map e), hb, Category.assoc]

private theorem coefficient_formula {U Y Z : C} {V Y' Z' : D}
    (b : V ⟶ F.obj U) (i : Y ⟶ Z) (c : F.obj Z ⟶ Z')
    (a : F.obj Y ⟶ Y') (j : Y' ⟶ Z') (hc : F.map i ≫ c = a ≫ j)
    (x : Ext.{z} U Y 0) :
    (Ext.mk₀ b).comp (((x.comp (Ext.mk₀ i) (add_zero 0)).mapExactFunctor F).comp
        (Ext.mk₀ c) (add_zero 0)) (zero_add 0) =
      ((Ext.mk₀ b).comp ((x.mapExactFunctor F).comp (Ext.mk₀ a) (add_zero 0))
        (zero_add 0)).comp (Ext.mk₀ j) (add_zero 0) := by
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective U Y).surjective x
  simp only [Ext.mk₀_comp_mk₀, Ext.mapExactFunctor_mk₀, F.map_comp]
  apply congrArg Ext.mk₀
  simp only [Category.assoc]
  rw [hc]

variable (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R]
  (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (γ : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun I => (ModuleCat.hasColimitsOfSize.{z, t, 0, 0} R).has_colimits_of_shape (Discrete I)

local notation "m" => OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Transport.map F R P Q β γ

def totalMap : Total.total R P K ⟶ Total.total R Q L :=
  HomologicalComplex₂.total.map m (.up ℕ)

variable {Z : C} {W : D} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  (η : Q ⟶ (ChainComplex.single₀ D).obj W)
  (g : W ⟶ F.obj Z) (hβ : β.f 0 ≫ F.map (ε.f 0) = η.f 0 ≫ g)

include hβ in
theorem source_component (b : ℕ) :
    Total.component R P ε K b ≫ ((m).f b).f 0 =
      (AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F Z g γ).f b ≫
        Total.component R Q η L b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Transport.map_apply F R P Q β γ b 0
    ((Ext.mk₀ (ε.f 0)).comp x (zero_add 0))).trans
      (source_formula F (ε.f 0) (β.f 0) (η.f 0) g (γ.f b) hβ x)

include hβ in
theorem source_edge : Total.edge R P ε K ≫ totalMap F R P Q β γ =
    AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F Z g γ ≫
      Total.edge R Q η L :=
  BicomplexHorizontalEdge.naturality _ _
    (Total.component R P ε K) (Total.vertical R P ε K)
    (Total.horizontal R P ε K) _ _
    (Total.component R Q η L) (Total.vertical R Q η L)
    (Total.horizontal R Q η L) m
    (AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F Z g γ)
    (source_component F R P Q β γ ε η g hβ)

variable {Y : C} {Y' : D} (ι : (CochainComplex.single₀ C).obj Y ⟶ K)
  (κ : (CochainComplex.single₀ D).obj Y' ⟶ L)
  (a : F.obj Y ⟶ Y') (hγ : F.map (ι.f 0) ≫ γ.f 0 = a ≫ κ.f 0)

def coefficientMap : Acyclic.ChainCohomology.complex R Y P ⟶
    Acyclic.ChainCohomology.complex R Y' Q :=
  Transport.rowMap F R P Q β Y ≫
    Acyclic.ChainCoefficientNaturality.complexMap R a Q

theorem coefficientMap_apply (b : ℕ) (x : Ext.{z} (P.X b) Y 0) :
    (coefficientMap F R P Q β a).f b x =
      (Ext.mk₀ (β.f b)).comp ((x.mapExactFunctor F).comp (Ext.mk₀ a) (add_zero 0)) (zero_add 0) :=
  Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (β.f b)) (x.mapExactFunctor F)
    (Ext.mk₀ a) (zero_add 0)

include hγ in
theorem coefficient_row : CoefficientEdge.rowMap R P K ι ≫ (m).f 0 =
    coefficientMap F R P Q β a ≫ CoefficientEdge.rowMap R Q L κ := by
  apply HomologicalComplex.Hom.ext
  funext b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Transport.map_apply F R P Q β γ 0 b
    (x.comp (Ext.mk₀ (ι.f 0)) (add_zero 0))).trans
      ((coefficient_formula F (β.f b) (ι.f 0) (γ.f 0) a (κ.f 0) hγ x).trans
        (congrArg (fun e : Ext.{z} (Q.X b) Y' 0 => e.comp (Ext.mk₀ (κ.f 0)) (add_zero 0))
          (coefficientMap_apply F R P Q β a b x).symm))

include hγ in
theorem coefficient_edge : CoefficientEdge.edge R P K ι ≫ totalMap F R P Q β γ =
    coefficientMap F R P Q β a ≫ CoefficientEdge.edge R Q L κ :=
  BicomplexCoefficientEdge.naturality _ _
    (CoefficientEdge.rowMap R P K ι) (CoefficientEdge.closed R P K ι)
    _ (CoefficientEdge.rowMap R Q L κ) (CoefficientEdge.closed R Q L κ)
    m (coefficientMap F R P Q β a) (coefficient_row F R P Q β γ ι κ a hγ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.TransportEdges
