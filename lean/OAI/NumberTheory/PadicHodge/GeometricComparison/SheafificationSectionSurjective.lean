import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf

/-! # Sheafification Section Surjective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionSurjective.SheafificationSectionSurjectivity

noncomputable section

/-! Surjectivity of presheaf sections passes to sheafified sections where the target unit is invertible. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type*) [CommRing R] [HasSheafify J (ModuleCat R)]
  {P Q : Cᵒᵖ ⥤ ModuleCat R} (f : P ⟶ Q) (U : Cᵒᵖ)

theorem surjective (hf : Function.Surjective (f.app U)) [IsIso ((toSheafify J Q).app U)] :
    Function.Surjective ((sheafifyMap J f).app U) := by
  intro y
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((toSheafify J Q).app U)).surjective y
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨(toSheafify J P).app U a, ?_⟩
  exact (ConcreteCategory.congr_hom (congrArg (fun g => g.app U) (toSheafify_naturality J f)) a).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionSurjective.SheafificationSectionSurjectivity
