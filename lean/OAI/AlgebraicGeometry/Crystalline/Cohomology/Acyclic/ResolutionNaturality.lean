import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution

/-! # Resolution Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionNaturality.AcyclicResolutionNaturality

noncomputable section

/-! # Naturality of the original positive-degree acyclic resolution comparison -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {K L : CochainComplex C ℕ} (f : K ⟶ L) {Z Z' : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ C).obj Z' ⟶ L) [QuasiIso κ]
  (a : Z ⟶ Z') (ha : ι ≫ f = (CochainComplex.single₀ C).map a ≫ κ)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} X (L.X j) (q + 1)))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

def sectionMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K ⟶
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X L :=
  ((F).mapHomologicalComplex (.up ℕ)).map f

include ha in
theorem short_naturality (n : ℕ) (x : ((NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).map F).homology) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X L κ hL n).hom
      (ShortComplex.homologyMap ((F).mapShortComplex.map (AugmentedResolution.AugmentedResolutionMaps.differentialMap f n)) x) =
    (Ext.mk₀ a).postcomp X (add_zero _)
      ((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X K ι hK n).hom x) := by
  cases n with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) 1) := hK 0 0
    let : Subsingleton (Ext.{z} X (L.X 0) 1) := hL 0 0
    have h := HomologyDataNaturality.AcyclicHomologyDataNaturality.homologyIso_naturality R X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K 0) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L 0) (AugmentedResolution.AugmentedResolutionMaps.differentialMap f 0)
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence K ι).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation L κ) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence L κ).zero
      a (AugmentedResolution.AugmentedResolutionMaps.augmentation_square f ι κ a ha).symm
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact L κ)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x
  | succ n =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) 1) := hK (n + 1) 0
    let : Subsingleton (Ext.{z} X (L.X (n + 1)) 1) := hL (n + 1) 0
    let β := ShortComplex.cyclesMap (AugmentedResolution.AugmentedResolutionMaps.differentialMap f n)
    let eK := NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
    let eL := NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    have hd := HomologyDataNaturality.AcyclicHomologyDataNaturality.homologyIso_naturality R X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1)) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L (n + 1))
      (AugmentedResolution.AugmentedResolutionMaps.differentialMap f (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n).zero β
      (ShortComplex.cyclesMap_i (AugmentedResolution.AugmentedResolutionMaps.differentialMap f n))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    have hd' : eL.hom (ShortComplex.homologyMap
        ((F).mapShortComplex.map (AugmentedResolution.AugmentedResolutionMaps.differentialMap f (n + 1))) x) =
        (Ext.mk₀ β).postcomp X (add_zero 1) (eK.hom x) :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd) x
    have hn : n + 0 + 2 = n + 1 + 1 := by omega
    let sK : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles 1 ≃ₗ[R] Ext.{z} X Z (n + 1 + 1) :=
      hn ▸ NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n 0
    let sL : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n).cycles 1 ≃ₗ[R] Ext.{z} X Z' (n + 1 + 1) :=
      hn ▸ NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X L κ hL n 0
    have hs := CycleShiftNaturality.AcyclicCycleShiftNaturality.cast_naturality R hn
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n 0)
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X L κ hL n 0)
      ((Ext.mk₀ β).postcomp X (add_zero 1)) a (eK.hom x)
      (CycleShiftNaturality.AcyclicCycleShiftNaturality.naturality R X f ι κ a ha hK hL n 0 (eK.hom x))
    change sL (eL.hom _) = (Ext.mk₀ a).postcomp X (add_zero _) (sK (eK.hom x))
    exact (congrArg sL hd').trans hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionNaturality.AcyclicResolutionNaturality
