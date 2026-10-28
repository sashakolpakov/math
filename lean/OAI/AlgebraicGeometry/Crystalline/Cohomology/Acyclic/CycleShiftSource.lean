import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift

/-! # Cycle Shift Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftSource.AcyclicCycleShiftSource

noncomputable section

/-! # Source naturality of the original acyclic dimension shifts -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

section Cast

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' Z : C}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem cast_naturality {d e : ℕ} (h : d = e)
    (s : M ≃ₗ[R] Ext.{z} X Z d) (t : N ≃ₗ[R] Ext.{z} X' Z d)
    (f : M → N) (u : X' ⟶ X) (x : M)
    (hx : t (f x) = (Ext.mk₀ u).precomp Z (zero_add d) (s x)) :
    (show N ≃ₗ[R] Ext.{z} X' Z e from h ▸ t) (f x) =
      (Ext.mk₀ u).precomp Z (zero_add e) ((show M ≃ₗ[R] Ext.{z} X Z e from h ▸ s) x) := by
  subst e
  exact hx

end Cast

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hK' : ∀ j q, Subsingleton (Ext.{z} X' (K.X j) (q + 1)))

theorem naturality (n q : ℕ) (α : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X' K ι hK' n q
      ((Ext.mk₀ u).precomp (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles (zero_add _) α) =
      (Ext.mk₀ u).precomp Z (zero_add _)
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n q α) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} X' (K.X 0) (q + 1)) := hK' 0 q
    let : Subsingleton (Ext.{z} X' (K.X 0) (q + 1 + 1)) := hK' 0 (q + 1)
    have h := ExtSource.ExtSourceSections.connecting u (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) α
    have hh := cast_naturality R (show q + 1 + 1 = 0 + q + 2 by omega)
      (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X' (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      ((Ext.mk₀ u).precomp (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K 0).cycles (zero_add _)) u α h
    simpa only [NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv, Nat.recAux, Nat.rec_zero] using hh
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} X' (K.X (n + 1)) (q + 1)) := hK' (n + 1) q
    let : Subsingleton (Ext.{z} X' (K.X (n + 1)) (q + 1 + 1)) := hK' (n + 1) (q + 1)
    have h := ExtSource.ExtSourceSections.connecting u (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α
    have h' := (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X' K ι hK' n (q + 1)) h).trans
      (ih (q + 1) (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α))
    have hh := cast_naturality R (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n (q + 1)))
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X' (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X' K ι hK' n (q + 1)))
      ((Ext.mk₀ u).precomp (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K (n + 1)).cycles (zero_add _)) u α h'
    simpa only [NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv, Nat.recAux, Nat.rec_add_one] using hh

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftSource.AcyclicCycleShiftSource
