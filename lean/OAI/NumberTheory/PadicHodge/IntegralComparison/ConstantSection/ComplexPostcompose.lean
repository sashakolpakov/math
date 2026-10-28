import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality
import Mathlib.Algebra.Homology.QuasiIso

/-! # Complex Postcompose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexPostcompose

noncomputable section

/-! Canonical constant-sheaf sections commute literally with
postcomposition into the original injective section complex. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  (M : CochainComplex (ModuleCat.{w} R) ℕ)
  {K L : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ}
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶ K)
  (g : K ⟶ L)

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections.constantUnit R J) 0

theorem map : ComplexMap.map R J M K a ≫
    ((E).mapHomologicalComplex (.up ℕ)).map g =
      ComplexMap.map R J M L (a ≫ g) := by
  have h := ComplexNaturality.naturality.{u,v,w,z}
    R J (𝟙 M) g a (a ≫ g) (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

include a g in
theorem quasiIso
    (h : QuasiIso (ComplexMap.map R J M K a ≫
      ((E).mapHomologicalComplex (.up ℕ)).map g)) :
    QuasiIso (ComplexMap.map R J M L (a ≫ g)) :=
  ComplexPostcompose.map R J M a g ▸ h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexPostcompose
