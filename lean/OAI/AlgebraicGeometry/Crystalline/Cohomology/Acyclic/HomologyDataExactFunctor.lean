import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData

/-! # Homology Data Exact Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataExactFunctor.AcyclicHomologyDataExactFunctor

noncomputable section

/-! # Exact-functor compatibility of the original acyclic homology data -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C) (T : ShortComplex C) (U : ShortComplex D) (φ : T.map F ⟶ U)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) 0

def sectionMap : T.map G ⟶ U.map H where
  τ₁ := ExactFunctor.ExactFunctorExtSections.map R F X φ.τ₁ 0
  τ₂ := ExactFunctor.ExactFunctorExtSections.map R F X φ.τ₂ 0
  τ₃ := ExactFunctor.ExactFunctorExtSections.map R F X φ.τ₃ 0
  comm₁₂ := (ExactFunctor.ExactFunctorExtSections.square R F X T.f U.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm 0).symm
  comm₂₃ := (ExactFunctor.ExactFunctorExtSections.square R F X T.g U.g φ.τ₂ φ.τ₃ φ.comm₂₃.symm 0).symm

variable {A : C} {B : D}
  (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (b : B ⟶ U.X₁) (hb : b ≫ U.toCycles = 0)
  (β : F.obj A ⟶ B) (hβ : β ≫ b = F.map a ≫ φ.τ₁)

def sequenceMap : (ShortComplex.mk a T.toCycles ha).map F ⟶ ShortComplex.mk b U.toCycles hb where
  τ₁ := β
  τ₂ := φ.τ₁
  τ₃ := ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ
  comm₁₂ := hβ
  comm₂₃ := (ExactResolution.ExactResolutionCycleMaps.toCycles_naturality F φ).symm

variable (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  (hU : (ShortComplex.mk b U.toCycles hb).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} (F.obj X) U.X₁ 1)]

local notation "dT" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hT
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R (F.obj X) U b hb hU

def data : ShortComplex.LeftHomologyMapData (sectionMap R F X T U φ) dT dU where
  φK := ExactFunctor.ExactFunctorExtSections.map R F X (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) 0
  φH := ExactFunctor.ExactFunctorExtSections.map R F X β 1
  commi := (ExactFunctor.ExactFunctorExtSections.square R F X T.iCycles U.iCycles
    (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) φ.τ₂ (ExactResolution.ExactResolutionCycleMaps.cyclesMap_i F φ).symm 0).symm
  commf' := by
    let c : (G).obj T.cycles ⟶ (H).obj U.cycles :=
      ExactFunctor.ExactFunctorExtSections.map R F X (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) 0
    let d : (G).obj T.X₁ ⟶ (H).obj U.X₁ := ExactFunctor.ExactFunctorExtSections.map R F X φ.τ₁ 0
    have ht : (dT).f' = (G).map T.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T
    have hu : (dU).f' = (H).map U.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R (F.obj X) U
    have hc : (G).map T.toCycles ≫ c = d ≫ (H).map U.toCycles :=
      ExactFunctor.ExactFunctorExtSections.square R F X T.toCycles U.toCycles φ.τ₁
        (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) (ExactResolution.ExactResolutionCycleMaps.toCycles_naturality F φ) 0
    exact (congrArg (fun g : (G).obj T.X₁ ⟶ (G).obj T.cycles => g ≫ c) ht).trans
      (hc.trans (congrArg (fun g : (H).obj U.X₁ ⟶ (H).obj U.cycles => d ≫ g) hu).symm)
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact (ExtExact.ExtExactFunctorConnecting.connecting F X hT hU (sequenceMap F T U φ a ha b hb β hβ) 0 α).symm

include hβ in
theorem homologyIso_naturality :
    ShortComplex.homologyMap (sectionMap R F X T U φ) ≫
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R (F.obj X) U b hb hU).hom =
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X T a ha hT).hom ≫
          ExactFunctor.ExactFunctorExtSections.map R F X β 1 :=
  (data R F X T U φ a ha b hb β hβ hT hU).homologyMap_comm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataExactFunctor.AcyclicHomologyDataExactFunctor
