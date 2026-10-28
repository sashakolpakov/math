import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.DegreeChartExtensions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions

/-! # Extension Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Preservation of chart-extension ratios under degree transitions, and uniform
stabilization of finitely many equalities after applying those transitions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} {L : Y.Modules}

/-- Applying the global degree transition to a chart numerator preserves its
prescribed ratio on that chart's part of `D(s)`. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.transition (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))
    (n m : ℕ) (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) :
    Common.DegreeChartExtensions.ChartPowerExtends f s r (n + m)
      (t ≫ (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m)) := by
  let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have h₀ : IsIso (Ample.LineBundles.pullbackSection D.ι (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Power.SectionTransport.iteratedPullback_power_isIso f n D.ι s
  have h₁ : IsIso (Ample.LineBundles.pullbackSection D.ι (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s (n + m)))) :=
    Power.SectionTransport.iteratedPullback_power_isIso f (n + m) D.ι s
  have he : Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n) ≫
      (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m) =
        Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s (n + m)) :=
    (Power.SectionTransitions.pullbackSection_postcomp f _ _).symm.trans
      (congrArg (Ample.LineBundles.pullbackSection f) (Power.SectionTransitions.tensorPowerSection_transition s n m))
  exact (Power.SectionTransitions.frameCoordinate_pullback_postcomp D.ι _ _ _ he t).trans ht

/-- Once a mapped transition makes a numerator zero, every longer transition does too. -/
theorem Chart.ExtensionTransitions.mappedPowerSectionTransition_zero_mono (F : Y.Modules ⥤ X.Modules)
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) {P : X.Modules}
    (t : P ⟶ F.obj (TensorPower.PowerSheaf.tensorPowerModule L n)) {m k : ℕ}
    (hm : t ≫ F.map (Power.SectionTransitions.powerSectionTransition s n m) = 0) (hmk : m ≤ k) :
    t ≫ F.map (Power.SectionTransitions.powerSectionTransition s n k) = 0 := by
  induction k, hmk using Nat.le_induction with
  | base => exact hm
  | succ k _ ih =>
    change t ≫ F.map (Power.SectionTransitions.powerSectionTransition s n k ≫ Section.PowerMultiplication.multiplyPowerBySection s (n + k)) = 0
    rw [F.map_comp, ← Category.assoc, ih, zero_comp]

/-- Equality after one mapped transition persists after every longer transition. -/
theorem Chart.ExtensionTransitions.mappedPowerSectionTransition_eq_mono (F : Y.Modules ⥤ X.Modules)
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) {P : X.Modules}
    (t t' : P ⟶ F.obj (TensorPower.PowerSheaf.tensorPowerModule L n)) {m k : ℕ}
    (hm : t ≫ F.map (Power.SectionTransitions.powerSectionTransition s n m) = t' ≫ F.map (Power.SectionTransitions.powerSectionTransition s n m))
    (hmk : m ≤ k) :
    t ≫ F.map (Power.SectionTransitions.powerSectionTransition s n k) = t' ≫ F.map (Power.SectionTransitions.powerSectionTransition s n k) := by
  have hz : (t - t') ≫ F.map (Power.SectionTransitions.powerSectionTransition s n m) = 0 := by
    rw [Preadditive.sub_comp, hm, sub_self]
  have hk := Chart.ExtensionTransitions.mappedPowerSectionTransition_zero_mono F s n (t - t') hz hmk
  exact sub_eq_zero.mp ((Preadditive.sub_comp _ _ _).symm.trans hk)

/-- A finite family of eventual equalities, possibly in different chart module
categories, has a common transition length at which all equalities hold. -/
theorem Chart.ExtensionTransitions.mappedPowerSectionTransition_eq_uniform {ι : Type v} [Fintype ι]
    (T : ι → Scheme.{u}) (F : ∀ i, Y.Modules ⥤ (T i).Modules)
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (t t' : ∀ i, Line.Bundles.structureModule (T i) ⟶ (F i).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (h : ∀ i, ∃ m : ℕ, t i ≫ (F i).map (Power.SectionTransitions.powerSectionTransition s n m) =
      t' i ≫ (F i).map (Power.SectionTransitions.powerSectionTransition s n m)) :
    ∃ m : ℕ, ∀ i, t i ≫ (F i).map (Power.SectionTransitions.powerSectionTransition s n m) =
      t' i ≫ (F i).map (Power.SectionTransitions.powerSectionTransition s n m) := by
  classical
  choose m hm using h
  exact ⟨Finset.univ.sup m, fun i => Chart.ExtensionTransitions.mappedPowerSectionTransition_eq_mono (F i) s n
    (t i) (t' i) (hm i) (Finset.le_sup (f := m) (Finset.mem_univ i))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
