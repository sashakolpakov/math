import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtExact

/-! # Cycle Shift Exact Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftExactFunctor.AcyclicCycleShiftExactFunctor

noncomputable section

/-! # Exact-functor naturality of the original acyclic dimension shifts -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z u' v' z' t

section Cast

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Z : C} {Z' : D}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem cast_naturality {d e : ℕ} (h : d = e)
    (s : M ≃ₗ[R] Ext.{z} X Z d) (t : N ≃ₗ[R] Ext.{z'} (F.obj X) Z' d)
    (f : M → N) (a : F.obj Z ⟶ Z') (x : M)
    (hx : t (f x) = (Ext.mk₀ a).postcomp (F.obj X) (add_zero d) ((s x).mapExactFunctor F)) :
    (show N ≃ₗ[R] Ext.{z'} (F.obj X) Z' e from h ▸ t) (f x) =
      (Ext.mk₀ a).postcomp (F.obj X) (add_zero e) (((show M ≃ₗ[R] Ext.{z} X Z e from h ▸ s) x).mapExactFunctor F) := by
  subst e
  exact hx

end Cast

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : C)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z'} (F.obj X) (L.X j) (q + 1)))

include ha in
theorem naturality (n q : ℕ) (α : Ext.{z} X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n q
      ((Ext.mk₀ (ExactResolution.ExactResolutionCycleMaps.cyclesMap F (ExactResolution.ExactResolutionCycleMaps.differentialMap F f n))).postcomp (F.obj X) (add_zero _) (α.mapExactFunctor F)) =
    (Ext.mk₀ a).postcomp (F.obj X) (add_zero _)
      ((NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n q α).mapExactFunctor F) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z'} (F.obj X) (L.X 0) (q + 1)) := hL 0 q
    let : Subsingleton (Ext.{z'} (F.obj X) (L.X 0) (q + 1 + 1)) := hL 0 (q + 1)
    have h := ExtExact.ExtExactFunctorConnecting.connecting F X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact L κ)
      (ExactResolution.ExactResolutionCycleMaps.initialMap F f ι κ a ha) (q + 1) α
    have hh := cast_naturality R F (show q + 1 + 1 = 0 + q + 2 by omega)
      (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence (F.obj X) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence_shortExact L κ) (q + 1) R)
      (fun x => (Ext.mk₀ (ExactResolution.ExactResolutionCycleMaps.cyclesMap F (ExactResolution.ExactResolutionCycleMaps.differentialMap F f 0))).postcomp
        (F.obj X) (add_zero _) (x.mapExactFunctor F)) a α h
    simpa only [NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv, Nat.recAux, Nat.rec_zero] using hh
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z'} (F.obj X) (L.X (n + 1)) (q + 1)) := hL (n + 1) q
    let : Subsingleton (Ext.{z'} (F.obj X) (L.X (n + 1)) (q + 1 + 1)) := hL (n + 1) (q + 1)
    have h := ExtExact.ExtExactFunctorConnecting.connecting F X
      (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
      (ExactResolution.ExactResolutionCycleMaps.successiveMap F f n) (q + 1) α
    have h' := (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n (q + 1)) h).trans
      (ih (q + 1) (NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α))
    have hh := cast_naturality R F (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence X (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R X K ι hK n (q + 1)))
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.linearEquivalence (F.obj X) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence_shortExact L κ n) (q + 1) R).trans
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n (q + 1)))
      (fun x => (Ext.mk₀ (ExactResolution.ExactResolutionCycleMaps.cyclesMap F (ExactResolution.ExactResolutionCycleMaps.differentialMap F f (n + 1)))).postcomp
        (F.obj X) (add_zero _) (x.mapExactFunctor F)) a α h'
    simpa only [NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift.cycleExtEquiv, Nat.recAux, Nat.rec_add_one] using hh

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.CycleShiftExactFunctor.AcyclicCycleShiftExactFunctor
