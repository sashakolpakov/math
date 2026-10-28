import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Triangle Saturated -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleSaturated.TriangleSaturatedImage

noncomputable section

/-! A torsion-free third Hom group makes the first image in a distinguished triangle saturated. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

universe u v

variable (R : Type*) [CommRing R] [IsDomain R] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear R C]

theorem quotient_torsionFree (T : Triangle C) (hT : T ∈ distTriang C) (A : C)
    [Module.IsTorsionFree R (A ⟶ T.obj₃)] :
    Module.IsTorsionFree R ((A ⟶ T.obj₂) ⧸ (Linear.rightComp R A T.mor₁).range) := by
  let P := (Linear.rightComp R A T.mor₁).range
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨m, rfl⟩ := P.mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero P).mpr
  have hm : r • m ∈ P := (Submodule.Quotient.mk_eq_zero P).mp
    (show P.mkQ (r • m) = 0 by simpa only [map_smul] using hx)
  obtain ⟨a, ha⟩ := hm
  have hz : r • (m ≫ T.mor₂) = 0 := by
    rw [← Linear.smul_comp, ← ha]
    change (a ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  have hmzero : m ≫ T.mor₂ = 0 := (smul_eq_zero.mp hz).resolve_left hr
  obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT m hmzero
  exact ⟨a, ha.symm⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TriangleSaturated.TriangleSaturatedImage
