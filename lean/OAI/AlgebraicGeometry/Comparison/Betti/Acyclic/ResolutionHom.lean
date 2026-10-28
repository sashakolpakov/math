import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionCycles

/-! # Resolution Hom -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionHom.Ext

noncomputable section

/-! Morphisms into an exact resolution by Ext-acyclic objects form an exact positive-degree complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (K : CochainComplex C ℕ) {F : C} (e : F ⟶ K.X 0) (w : e ≫ K.d 0 1 = 0)

theorem acyclicResolution_hom_exact_succ [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (ResolutionCycles.Ext.resolutionSequence K n).Exact)
    (hF : ∀ q, Subsingleton (Ext A F (q + 1)))
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1)))
    (n : ℕ) (z : A ⟶ K.X (n + 1)) (hz : z ≫ K.d (n + 1) (n + 2) = 0) :
    ∃ y : A ⟶ K.X n, y ≫ K.d n (n + 1) = z := by
  let T := ResolutionCycles.Ext.resolutionSequence K n
  let c : A ⟶ T.cycles := T.liftCycles z hz
  have hl : ∃ y : A ⟶ K.X n, y ≫ T.toCycles = c := by
    cases n with
    | zero =>
      have : Subsingleton (Ext A F 1) := hF 0
      exact ExtVanishing.hom_lift_of_ext_one A (ResolutionCycles.Ext.initialCycleSequence_shortExact K e w haug hpos) c
    | succ n =>
      have : Subsingleton (Ext A (ResolutionCycles.Ext.resolutionSequence K n).cycles 1) :=
        ResolutionCycles.Ext.resolutionCycles_ext_vanish A K e w haug hpos hF hK n 0
      exact ExtVanishing.hom_lift_of_ext_one A (ResolutionCycles.Ext.successiveCycleSequence_shortExact K hpos n) c
  obtain ⟨y, hy⟩ := hl
  refine ⟨y, ?_⟩
  change y ≫ T.f = z
  rw [← T.toCycles_i, ← Category.assoc, hy]
  exact T.liftCycles_i z hz

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionHom.Ext
