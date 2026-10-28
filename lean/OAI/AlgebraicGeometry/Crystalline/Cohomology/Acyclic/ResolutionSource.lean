import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution

/-! # Resolution Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionSource.AcyclicResolutionSource

noncomputable section

/-! # Source naturality of the original positive acyclic-resolution comparison -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hK' : ∀ j q, Subsingleton (Ext.{z} X' (K.X j) (q + 1)))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

theorem short_naturality (n : ℕ) (x : ((NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).map F).homology) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X' K ι hK' n).hom
      (ShortComplex.homologyMap (HomologyDataSource.AcyclicHomologyDataSource.sectionMap R u (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n)) x) =
    (Ext.mk₀ u).precomp Z (zero_add _)
      ((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X K ι hK n).hom x) := by
  cases n with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) 1) := hK 0 0
    let : Subsingleton (Ext.{z} X' (K.X 0) 1) := hK' 0 0
    have h := HomologyDataSource.AcyclicHomologyDataSource.homologyIso_naturality R u (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K 0)
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence K ι).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x
  | succ n =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) 1) := hK (n + 1) 0
    let : Subsingleton (Ext.{z} X' (K.X (n + 1)) 1) := hK' (n + 1) 0
    let eX := NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
    let eX' := NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X' (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
    have hd := HomologyDataSource.AcyclicHomologyDataSource.homologyIso_naturality R u (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).f (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).zero (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
    have hd' : eX'.hom (ShortComplex.homologyMap
        (HomologyDataSource.AcyclicHomologyDataSource.sectionMap R u (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1))) x) =
        (Ext.mk₀ u).precomp (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles (zero_add 1) (eX.hom x) :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hd) x
    have hn : n + 0 + 2 = n + 1 + 1 := by omega
    let sX : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles 1 ≃ₗ[R] Ext.{z} X Z (n + 1 + 1) :=
      hn ▸ NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n 0
    let sX' : Ext.{z} X' (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles 1 ≃ₗ[R] Ext.{z} X' Z (n + 1 + 1) :=
      hn ▸ NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X' K ι hK' n 0
    have hs := CycleShiftSource.AcyclicCycleShiftSource.cast_naturality R hn
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n 0)
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X' K ι hK' n 0)
      ((Ext.mk₀ u).precomp (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles (zero_add 1)) u (eX.hom x)
      (CycleShiftSource.AcyclicCycleShiftSource.naturality R u K ι hK hK' n 0 (eX.hom x))
    change sX' (eX'.hom _) = (Ext.mk₀ u).precomp Z (zero_add _) (sX (eX.hom x))
    exact (congrArg sX' hd').trans hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionSource.AcyclicResolutionSource
