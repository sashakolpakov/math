import OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentedResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

/-! # Cycle Shift Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftNaturality.AcyclicCycleShiftNaturality

noncomputable section

/-! # Naturality of dimension shifting along the actual augmented cycle sequences -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

section Cast

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X Z Z' : C}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem cast_naturality {d e : ℕ} (h : d = e)
    (s : M ≃ₗ[R] Ext.{z} X Z d) (t : N ≃ₗ[R] Ext.{z} X Z' d)
    (f : M → N) (a : Z ⟶ Z') (x : M)
    (hx : t (f x) = (Ext.mk₀ a).postcomp X (add_zero d) (s x)) :
    (show N ≃ₗ[R] Ext.{z} X Z' e from h ▸ t) (f x) =
      (Ext.mk₀ a).postcomp X (add_zero e) ((show M ≃ₗ[R] Ext.{z} X Z e from h ▸ s) x) := by
  subst e
  exact hx

end Cast

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {K L : CochainComplex C ℕ} (f : K ⟶ L) {Z Z' : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ C).obj Z' ⟶ L) [QuasiIso κ]
  (a : Z ⟶ Z') (ha : ι ≫ f = (CochainComplex.single₀ C).map a ≫ κ)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} X (L.X j) (q + 1)))

include ha in
theorem naturality (n q : ℕ) (α : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X L κ hL n q
      ((Ext.mk₀ (ShortComplex.cyclesMap (AugmentedResolution.AugmentedResolutionMaps.differentialMap f n))).postcomp X (add_zero _) α) =
    (Ext.mk₀ a).postcomp X (add_zero _)
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n q α) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} X (L.X 0) (q + 1)) := hL 0 q
    let : Subsingleton (Ext.{z} X (L.X 0) (q + 1 + 1)) := hL 0 (q + 1)
    have h := NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality.connecting X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact L κ)
      (AugmentedResolution.AugmentedResolutionMaps.initialMap f ι κ a ha) (q + 1) α
    have hh := cast_naturality R (show q + 1 + 1 = 0 + q + 2 by omega)
      (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact L κ) (q + 1) R)
      ((Ext.mk₀ (ShortComplex.cyclesMap (AugmentedResolution.AugmentedResolutionMaps.differentialMap f 0))).postcomp X (add_zero _)) a α h
    simpa only [NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv, Nat.recAux, Nat.rec_zero] using hh
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} X (L.X (n + 1)) (q + 1)) := hL (n + 1) q
    let : Subsingleton (Ext.{z} X (L.X (n + 1)) (q + 1 + 1)) := hL (n + 1) (q + 1)
    have h := NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality.connecting X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
      (AugmentedResolution.AugmentedResolutionMaps.successiveMap f n) (q + 1) α
    have h' := (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X L κ hL n (q + 1)) h).trans
      (ih (q + 1) (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α))
    have hh := cast_naturality R (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n (q + 1)))
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n) (q + 1) R).trans
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X L κ hL n (q + 1)))
      ((Ext.mk₀ (ShortComplex.cyclesMap (AugmentedResolution.AugmentedResolutionMaps.differentialMap f (n + 1)))).postcomp X (add_zero _)) a α h'
    simpa only [NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv, Nat.recAux, Nat.rec_add_one] using hh

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftNaturality.AcyclicCycleShiftNaturality
