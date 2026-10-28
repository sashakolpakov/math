import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Sheafification Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationRestriction.SheafificationRestrictionGenerators

noncomputable section

/-! # Original sheafification generators on a sheaf-valued restriction -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Opposite

variable {C D A : Type*} [Category C] [Category D] [Category A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
  (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J (F.op ⋙ P))

include hP in
theorem restricted_isIso : IsIso (whiskerLeft F.op (toSheafify K P)) := by
  let := isIso_toSheafify J hP
  let e := (sheafToPresheaf J A).mapIso (NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence.transport J K F P)
  have h : IsIso (toSheafify J (F.op ⋙ P) ≫ e.inv) := inferInstance
  exact NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence.transport_generator J K F P ▸ h

include hP in
theorem component_isIso (Q : C) : IsIso ((toSheafify K P).app (op (F.obj Q))) := by
  let := restricted_isIso J K F P hP
  exact inferInstanceAs (IsIso ((whiskerLeft F.op (toSheafify K P)).app (op Q)))

universe u v

variable {R : Type u} [Ring R] {E : Type*} [Category E]
  {M N : E ⥤ ModuleCat.{v} R} (η : M ⟶ N) (L : ModuleCat.{v} R)
  (s : (Functor.const E).obj L ⟶ N) {Q Q' : E} (f : Q ⟶ Q') (z : L)

theorem section_generator (x : M.obj Q) (hx : (s.app Q).hom z = (η.app Q).hom x) :
    (s.app Q').hom z = (η.app Q').hom ((M.map f).hom x) := by
  have hs := ConcreteCategory.congr_hom (s.naturality f) z
  have hη := ConcreteCategory.congr_hom (η.naturality f) x
  change (s.app Q').hom z = (N.map f).hom ((s.app Q).hom z) at hs
  change (η.app Q').hom ((M.map f).hom x) = (N.map f).hom ((η.app Q).hom x) at hη
  exact hs.trans ((congrArg (N.map f).hom hx).trans hη.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationRestriction.SheafificationRestrictionGenerators
