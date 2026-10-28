import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

/-! # Exact Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactResolution.ExactResolutionCycleMaps

noncomputable section

/-! # Canonical cycle maps for resolutions transported by an exact functor -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section Short

variable {T : ShortComplex C} {U : ShortComplex D} (φ : T.map F ⟶ U)

def cyclesMap : F.obj T.cycles ⟶ U.cycles :=
  (T.mapCyclesIso F).inv ≫ ShortComplex.cyclesMap φ

theorem cyclesMap_i : ExactResolutionCycleMaps.cyclesMap F φ ≫ U.iCycles = F.map T.iCycles ≫ φ.τ₂ := by
  let e : (T.map F).cycles ≅ F.obj T.cycles := T.mapCyclesIso F
  let j : (T.map F).cycles ⟶ F.obj T.X₂ := (T.map F).iCycles
  let b : F.obj T.X₂ ⟶ U.X₂ := φ.τ₂
  let c : (T.map F).cycles ⟶ U.cycles := ShortComplex.cyclesMap φ
  have he : e.hom ≫ F.map T.iCycles = j := T.mapCyclesIso_hom_iCycles F
  have hc : c ≫ U.iCycles = j ≫ b := ShortComplex.cyclesMap_i φ
  change (e.inv ≫ c) ≫ U.iCycles = F.map T.iCycles ≫ b
  rw [Category.assoc, hc, ← he]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem toCycles_naturality : F.map T.toCycles ≫ ExactResolutionCycleMaps.cyclesMap F φ = φ.τ₁ ≫ U.toCycles := by
  let a : F.obj T.X₁ ⟶ U.X₁ := φ.τ₁
  let b : F.obj T.X₂ ⟶ U.X₂ := φ.τ₂
  have hc : ExactResolutionCycleMaps.cyclesMap F φ ≫ U.iCycles = F.map T.iCycles ≫ b := ExactResolutionCycleMaps.cyclesMap_i F φ
  change F.map T.toCycles ≫ ExactResolutionCycleMaps.cyclesMap F φ = a ≫ U.toCycles
  apply (cancel_mono U.iCycles).1
  rw [Category.assoc, hc, ← Category.assoc, ← F.map_comp,
    T.toCycles_i, Category.assoc, U.toCycles_i]
  exact φ.comm₁₂.symm

end Short

variable {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def differentialMap (n : ℕ) : (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n).map F ⟶ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n where
  τ₁ := f.f n
  τ₂ := f.f (n + 1)
  τ₃ := f.f (n + 2)
  comm₁₂ := f.comm n (n + 1)
  comm₂₃ := f.comm (n + 1) (n + 2)

def successiveMap (n : ℕ) : (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence K n).map F ⟶ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.successiveSequence L n where
  τ₁ := ExactResolutionCycleMaps.cyclesMap F (differentialMap F f n)
  τ₂ := f.f (n + 1)
  τ₃ := ExactResolutionCycleMaps.cyclesMap F (differentialMap F f (n + 1))
  comm₁₂ := ExactResolutionCycleMaps.cyclesMap_i F (differentialMap F f n)
  comm₂₃ := (toCycles_naturality F (differentialMap F f (n + 1))).symm

variable {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L)
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)

def initialMap : (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence K ι).map F ⟶ NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.initialSequence L κ where
  τ₁ := a
  τ₂ := f.f 0
  τ₃ := ExactResolutionCycleMaps.cyclesMap F (differentialMap F f 0)
  comm₁₂ := ha.symm
  comm₂₃ := (toCycles_naturality F (differentialMap F f 0)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactResolution.ExactResolutionCycleMaps
