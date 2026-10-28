import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution

/-! # Resolution Exact Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionExactFunctor.AcyclicResolutionExactFunctor

noncomputable section

/-! # Exact-functor naturality of the original positive-degree comparison -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} (F.obj X) (L.X j) (q + 1)))

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

def sectionMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K ⟶
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R (F.obj X) L :=
  ExactFunctor.ExactFunctorExtSections.complexMap R F X f

include ha in
theorem short_naturality (n : ℕ) (x : ((NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).map G).homology) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R (F.obj X) L κ hL n).hom
      (ShortComplex.homologyMap (HomologyDataExactFunctor.AcyclicHomologyDataExactFunctor.sectionMap R F X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n)
        (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n) (ExactResolution.ExactResolutionCycleMaps.differentialMap F f n)) x) =
    (Ext.mk₀ a).postcomp (F.obj X) (add_zero _)
      (((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X K ι hK n).hom x).mapExactFunctor F) := by
  cases n with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) 1) := hK 0 0
    let : Subsingleton (Ext.{z} (F.obj X) (L.X 0) 1) := hL 0 0
    have h := HomologyDataExactFunctor.AcyclicHomologyDataExactFunctor.homologyIso_naturality R F X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K 0) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L 0) (ExactResolution.ExactResolutionCycleMaps.differentialMap F f 0)
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence K ι).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation L κ) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence L κ).zero
      a ha.symm
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact L κ)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x
  | succ n =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) 1) := hK (n + 1) 0
    let : Subsingleton (Ext.{z} (F.obj X) (L.X (n + 1)) 1) := hL (n + 1) 0
    let β := ExactResolution.ExactResolutionCycleMaps.cyclesMap F (ExactResolution.ExactResolutionCycleMaps.differentialMap F f n)
    let eK := NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
    let eL := NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R (F.obj X) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    have hd := HomologyDataExactFunctor.AcyclicHomologyDataExactFunctor.homologyIso_naturality R F X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1)) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L (n + 1))
      (ExactResolution.ExactResolutionCycleMaps.differentialMap F f (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).zero β
      (ExactResolution.ExactResolutionCycleMaps.cyclesMap_i F (ExactResolution.ExactResolutionCycleMaps.differentialMap F f n))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    have hd' : eL.hom (ShortComplex.homologyMap
        (HomologyDataExactFunctor.AcyclicHomologyDataExactFunctor.sectionMap R F X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))
          (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L (n + 1)) (ExactResolution.ExactResolutionCycleMaps.differentialMap F f (n + 1))) x) =
        (Ext.mk₀ β).postcomp (F.obj X) (add_zero 1) ((eK.hom x).mapExactFunctor F) :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd) x
    have hn : n + 0 + 2 = n + 1 + 1 := by omega
    let sK : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles 1 ≃ₗ[R] Ext.{z} X Z (n + 1 + 1) :=
      hn ▸ NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n 0
    let sL : Ext.{z} (F.obj X) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n).cycles 1 ≃ₗ[R] Ext.{z} (F.obj X) Z' (n + 1 + 1) :=
      hn ▸ NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n 0
    have hs := CycleShiftExactFunctor.AcyclicCycleShiftExactFunctor.cast_naturality R F hn
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n 0)
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n 0)
      (fun y => (Ext.mk₀ β).postcomp (F.obj X) (add_zero 1) (y.mapExactFunctor F)) a (eK.hom x)
      (CycleShiftExactFunctor.AcyclicCycleShiftExactFunctor.naturality R F X f ι κ a ha hK hL n 0 (eK.hom x))
    change sL (eL.hom _) = (Ext.mk₀ a).postcomp (F.obj X) (add_zero _) ((sK (eK.hom x)).mapExactFunctor F)
    exact (congrArg sL hd').trans hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionExactFunctor.AcyclicResolutionExactFunctor
