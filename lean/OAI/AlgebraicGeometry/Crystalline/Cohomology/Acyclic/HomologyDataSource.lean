import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData

/-! # Homology Data Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataSource.AcyclicHomologyDataSource

noncomputable section

/-! # Source naturality of the original acyclic homology data -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X) (T : ShortComplex C)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X' 0
local notation "α" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource.ExtSourceSections.transformation R u 0

def sectionMap : T.map F ⟶ T.map G where
  τ₁ := (α).app T.X₁
  τ₂ := (α).app T.X₂
  τ₃ := (α).app T.X₃
  comm₁₂ := ((α).naturality T.f).symm
  comm₂₃ := ((α).naturality T.g).symm

variable {A : C} (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (hS : (ShortComplex.mk a T.toCycles ha).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} X' T.X₁ 1)]

local notation "dX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hS
local notation "dX'" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X' T a ha hS

def data : ShortComplex.LeftHomologyMapData (sectionMap R u T) dX dX' where
  φK := (α).app T.cycles
  φH := (ExtSource.ExtSourceSections.transformation R u 1).app A
  commi := ((α).naturality T.iCycles).symm
  commf' := by
    let c : (F).obj T.cycles ⟶ (G).obj T.cycles := (α).app T.cycles
    let d : (F).obj T.X₁ ⟶ (G).obj T.X₁ := (α).app T.X₁
    have hx : (dX).f' = (F).map T.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T
    have hx' : (dX').f' = (G).map T.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X' T
    have hc : (F).map T.toCycles ≫ c = d ≫ (G).map T.toCycles := (α).naturality T.toCycles
    exact (congrArg (fun g : (F).obj T.X₁ ⟶ (F).obj T.cycles => g ≫ c) hx).trans
      (hc.trans (congrArg (fun g : (G).obj T.X₁ ⟶ (G).obj T.cycles => d ≫ g) hx').symm)
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (ExtSource.ExtSourceSections.connecting u hS 0 x).symm

theorem homologyIso_naturality :
    ShortComplex.homologyMap (sectionMap R u T) ≫
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X' T a ha hS).hom =
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X T a ha hS).hom ≫
          (ExtSource.ExtSourceSections.transformation R u 1).app A :=
  (data R u T a ha hS).homologyMap_comm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataSource.AcyclicHomologyDataSource
