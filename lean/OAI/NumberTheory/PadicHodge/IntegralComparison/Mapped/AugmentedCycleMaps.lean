import OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor

/-! # Augmented Cycle Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.AugmentedCycleMaps

noncomputable section

/-! Maps from an exactly transported augmented resolution induce the actual
cycle-sequence maps, without acyclicity of the intermediate transported terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (φ : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def differential (i : ℕ) : (Augmented.ResolutionCycles.differentialSequence K i).map F ⟶ Augmented.ResolutionCycles.differentialSequence L i where
  τ₁ := φ.f i
  τ₂ := φ.f (i + 1)
  τ₃ := φ.f (i + 2)
  comm₁₂ := φ.comm i (i + 1)
  comm₂₃ := φ.comm (i + 1) (i + 2)

def cycles (i : ℕ) : F.obj (Augmented.ResolutionCycles.differentialSequence K i).cycles ⟶ (Augmented.ResolutionCycles.differentialSequence L i).cycles :=
  ShortCyclesExactFunctor.cycleMap F (differential F φ i)

theorem cycles_i (i : ℕ) : AugmentedCycleMaps.cycles F φ i ≫ (Augmented.ResolutionCycles.differentialSequence L i).iCycles =
    F.map (Augmented.ResolutionCycles.differentialSequence K i).iCycles ≫ φ.f (i + 1) :=
  ShortCyclesExactFunctor.cycleMap_i F (differential F φ i)

def successive (i : ℕ) : (Augmented.ResolutionCycles.successiveSequence K i).map F ⟶ Augmented.ResolutionCycles.successiveSequence L i where
  τ₁ := AugmentedCycleMaps.cycles F φ i
  τ₂ := φ.f (i + 1)
  τ₃ := AugmentedCycleMaps.cycles F φ (i + 1)
  comm₁₂ := cycles_i F φ i
  comm₂₃ := (ShortCyclesExactFunctor.toCycles F (differential F φ (i + 1))).symm

variable {Z : C} {W : D} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ D).obj W ⟶ L) (g : F.obj Z ⟶ W)
  (h : g ≫ κ.f 0 = F.map (ι.f 0) ≫ φ.f 0)

def initial : (Augmented.ResolutionCycles.initialSequence K ι).map F ⟶ Augmented.ResolutionCycles.initialSequence L κ where
  τ₁ := g
  τ₂ := φ.f 0
  τ₃ := AugmentedCycleMaps.cycles F φ 0
  comm₁₂ := h
  comm₂₃ := (ShortCyclesExactFunctor.toCycles F (differential F φ 0)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.AugmentedCycleMaps
