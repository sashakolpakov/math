import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

/-! # Augmented Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentedResolution.AugmentedResolutionMaps

noncomputable section

/-! # Maps of the canonical cycle sequences of augmented resolutions -/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ} (f : K ⟶ L)

def differentialMap (n : ℕ) : NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n ⟶ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n where
  τ₁ := f.f n
  τ₂ := f.f (n + 1)
  τ₃ := f.f (n + 2)
  comm₁₂ := f.comm n (n + 1)
  comm₂₃ := f.comm (n + 1) (n + 2)

def successiveMap (n : ℕ) : NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n ⟶ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n where
  τ₁ := ShortComplex.cyclesMap (differentialMap f n)
  τ₂ := f.f (n + 1)
  τ₃ := ShortComplex.cyclesMap (differentialMap f (n + 1))
  comm₁₂ := ShortComplex.cyclesMap_i (differentialMap f n)
  comm₂₃ := (ShortComplex.toCycles_naturality (differentialMap f (n + 1))).symm

variable {Z Z' : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ C).obj Z' ⟶ L)
  (a : Z ⟶ Z') (ha : ι ≫ f = (CochainComplex.single₀ C).map a ≫ κ)

include ha in
theorem augmentation_square : NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation K ι ≫ f.f 0 = a ≫ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation L κ := by
  have hh := congrArg (fun g => g.f 0) ha
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero] at hh
  exact hh

def initialMap : NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence K ι ⟶ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence L κ where
  τ₁ := a
  τ₂ := f.f 0
  τ₃ := ShortComplex.cyclesMap (differentialMap f 0)
  comm₁₂ := (augmentation_square f ι κ a ha).symm
  comm₂₃ := (ShortComplex.toCycles_naturality (differentialMap f 0)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentedResolution.AugmentedResolutionMaps
