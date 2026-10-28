import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

/-! # Resolution Cycle Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

noncomputable section

/-!
# IntegralComparison: maps of augmented resolutions induce the actual cycle-sequence maps
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ} (φ : K ⟶ L)

def differential (i : ℕ) : ResolutionCycles.differentialSequence K i ⟶ ResolutionCycles.differentialSequence L i where
  τ₁ := φ.f i
  τ₂ := φ.f (i + 1)
  τ₃ := φ.f (i + 2)
  comm₁₂ := φ.comm i (i + 1)
  comm₂₃ := φ.comm (i + 1) (i + 2)

def successive (i : ℕ) : ResolutionCycles.successiveSequence K i ⟶ ResolutionCycles.successiveSequence L i where
  τ₁ := ShortComplex.cyclesMap (differential φ i)
  τ₂ := φ.f (i + 1)
  τ₃ := ShortComplex.cyclesMap (differential φ (i + 1))
  comm₁₂ := ShortComplex.cyclesMap_i (differential φ i)
  comm₂₃ := (ShortComplex.toCycles_naturality (differential φ (i + 1))).symm

variable {Z W : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ C).obj W ⟶ L) (f : Z ⟶ W)
  (h : ι ≫ φ = (CochainComplex.single₀ C).map f ≫ κ)

include h

theorem augmentation : f ≫ ResolutionCycles.augmentation L κ =
    ResolutionCycles.augmentation K ι ≫ φ.f 0 := by
  exact (congrArg (fun a => a ≫ ResolutionCycles.augmentation L κ)
    (CochainComplex.single₀_map_f_zero f)).symm.trans (congrArg (fun a => a.f 0) h).symm

def initial : ResolutionCycles.initialSequence K ι ⟶ ResolutionCycles.initialSequence L κ where
  τ₁ := f
  τ₂ := φ.f 0
  τ₃ := ShortComplex.cyclesMap (differential φ 0)
  comm₁₂ := augmentation φ ι κ f h
  comm₂₃ := (ShortComplex.toCycles_naturality (differential φ 0)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps
