import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap

/-! # Complex Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexIso

noncomputable section

/-!
# IntegralComparison: degreewise section bijections identify the actual section complex
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  (D : CochainComplex (ModuleCat.{w} R) ℕ) (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ⟶ K)
  (ha : ∀ n, Function.Bijective (Module.ConstantSections.sectionMap R J (D.X n) (K.X n) (a.f n)))

include ha in
theorem component_isIso (n : ℕ) : IsIso ((ComplexMap.map R J D K a).f n) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ha n).comp (Equiv.ulift : ULift.{z} (D.X n) ≃ D.X n).bijective

include ha in
theorem map_isIso : IsIso (ComplexMap.map R J D K a) := by
  let (n : ℕ) : IsIso ((ComplexMap.map R J D K a).f n) := component_isIso R J D K a ha n
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexIso
