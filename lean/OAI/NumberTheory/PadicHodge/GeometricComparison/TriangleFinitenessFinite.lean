import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-! # Triangle Finiteness Finite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleFinitenessFinite.TriangleFiniteness

noncomputable section

/-! Finite outer Hom modules in a distinguished triangle give a finite middle Hom module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

universe u v

variable (R : Type*) [CommRing R] [IsNoetherianRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear R C]

theorem finite (T : Triangle C) (hT : T ∈ distTriang C) (A : C)
    [Module.Finite R (A ⟶ T.obj₁)] [Module.Finite R (A ⟶ T.obj₃)] :
    Module.Finite R (A ⟶ T.obj₂) := by
  let f := Linear.rightComp R A T.mor₁
  let g := Linear.rightComp R A T.mor₂
  have hker : g.ker = f.range := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT x hx
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, rfl⟩
      change (a ≫ T.mor₁) ≫ T.mor₂ = 0
      rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  let : Module.Finite R f.range := Module.Finite.range f
  let : Module.Finite R g.range :=
    Module.Finite.of_injective g.range.subtype Subtype.val_injective
  let : Module.Finite R ((A ⟶ T.obj₂) ⧸ f.range) := by
    rw [← hker]
    exact Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.range

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleFinitenessFinite.TriangleFiniteness
