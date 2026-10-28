import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CanonicalMap

/-! # Terminal Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TerminalScalars

noncomputable section

/-! When terminal coefficients are the original ring, the literal
scalar map on the dual Koszul complex is an isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c : ℕ} (s : Fin c → R)
  (h : Function.Bijective (algebraMap R (P.obj (op (⊤_ C)))))

include h in
theorem component_isIso (q : ℕ) :
    IsIso ((KoszulPartial.CanonicalMap.scalarsMap R P s).f q) := by
  let e := LinearEquiv.ofBijective (Algebra.linearMap R (P.obj (op (⊤_ C)))) h
  let E := LinearEquiv.congrRight (M :=
    ⋀[R]^q (KoszulPartial.Fractions.normal R (c := c))) e
  have he : (KoszulPartial.CanonicalMap.scalarsMap R P s).f q = E.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl
  rw [he]
  infer_instance

include h in
theorem isIso : IsIso (KoszulPartial.CanonicalMap.scalarsMap R P s) := by
  let (q : ℕ) := component_isIso R P s h q
  exact HomologicalComplex.Hom.isIso_of_components _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.TerminalScalars
