import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ExtSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Acyclic Homology Data -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData

noncomputable section

/-! # Original acyclic homology data under exact semilinear transport -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t t'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) (S : Type t') [CommRing R] [CommRing S] [Linear R C] [Linear S D]
  (σ : R →+* S) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
  (X : C) (T : ShortComplex C) (U : ShortComplex D) (φ : T.map F ⟶ U)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor S (F.obj X) 0

def coefficients : ModuleCat.{z} S ⥤ ModuleCat.{z} R := ModuleCat.restrictScalars σ

instance coefficients_additive : (coefficients R S σ).Additive := by
  unfold coefficients
  infer_instance

instance coefficients_preservesHomology : (coefficients R S σ).PreservesHomology := by
  unfold coefficients
  infer_instance

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R S σ

def sectionMap : T.map G ⟶ (U.map H).map Q where
  τ₁ := ExtSections.SemilinearExtSections.map R S σ F hF X φ.τ₁ 0
  τ₂ := ExtSections.SemilinearExtSections.map R S σ F hF X φ.τ₂ 0
  τ₃ := ExtSections.SemilinearExtSections.map R S σ F hF X φ.τ₃ 0
  comm₁₂ := (ExtSections.SemilinearExtSections.square R S σ F hF X T.f U.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm 0).symm
  comm₂₃ := (ExtSections.SemilinearExtSections.square R S σ F hF X T.g U.g φ.τ₂ φ.τ₃ φ.comm₂₃.symm 0).symm

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
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data S (F.obj X) U b hb hU

def data : ShortComplex.LeftHomologyMapData (sectionMap R S σ F hF X T U φ) dT ((dU).map Q) where
  φK := ExtSections.SemilinearExtSections.map R S σ F hF X (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) 0
  φH := ExtSections.SemilinearExtSections.map R S σ F hF X β 1
  commi := (ExtSections.SemilinearExtSections.square R S σ F hF X T.iCycles U.iCycles
    (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) φ.τ₂ (ExactResolution.ExactResolutionCycleMaps.cyclesMap_i F φ).symm 0).symm
  commf' := by
    rw [ShortComplex.LeftHomologyData.map_f']
    let c : (G).obj T.cycles ⟶ (Q).obj ((H).obj U.cycles) :=
      ExtSections.SemilinearExtSections.map R S σ F hF X (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) 0
    let d : (G).obj T.X₁ ⟶ (Q).obj ((H).obj U.X₁) := ExtSections.SemilinearExtSections.map R S σ F hF X φ.τ₁ 0
    have ht : (dT).f' = (G).map T.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T
    have hu : (dU).f' = (H).map U.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift S (F.obj X) U
    have hc : (G).map T.toCycles ≫ c = d ≫ (Q).map ((H).map U.toCycles) :=
      ExtSections.SemilinearExtSections.square R S σ F hF X T.toCycles U.toCycles φ.τ₁
        (ExactResolution.ExactResolutionCycleMaps.cyclesMap F φ) (ExactResolution.ExactResolutionCycleMaps.toCycles_naturality F φ) 0
    exact (congrArg (fun g : (G).obj T.X₁ ⟶ (G).obj T.cycles => g ≫ c) ht).trans
      (hc.trans (congrArg (fun g : (H).obj U.X₁ ⟶ (H).obj U.cycles => d ≫ (Q).map g) hu).symm)
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact (ExtExact.ExtExactFunctorConnecting.connecting F X hT hU
      (sequenceMap F T U φ a ha b hb β hβ) 0 α).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData
