import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCone

/-! # Local Cone Upper -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeUpper.SemilatticeLocalConeUpper

noncomputable section

/-! On a larger chart, the canonical local cone is the inverse
of restriction to its defining chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable (C : Type u) [SemilatticeInf C] (I : C)
  {A : Type v} [Category.{w} A] (P : Cᵒᵖ ⥤ A)
  (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (J : C) (hIJ : I ≤ J)

include h in
theorem restriction_isIso : IsIso (P.map (homOfLE hIJ).op) := by
  let e : I ≅ J ⊓ I :=
    { hom := homOfLE (le_inf hIJ le_rfl)
      inv := homOfLE inf_le_right
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ }
  let : IsIso (P.map (homOfLE (inf_le_left : J ⊓ I ≤ J)).op) := h J
  let : IsIso (P.map e.hom.op) := inferInstanceAs (IsIso (P.mapIso e.op).hom)
  have heq : P.map (homOfLE hIJ).op =
      P.map (homOfLE (inf_le_left : J ⊓ I ≤ J)).op ≫ P.map e.hom.op := by
    rw [← P.map_comp]
    exact congrArg P.map (Subsingleton.elim _ _)
  rw [heq]
  infer_instance

theorem app_restriction : (LocalCone.SemilatticeLocalCone.cone C I P h).app (op J) ≫
    P.map (homOfLE hIJ).op = 𝟙 (P.obj (op I)) :=
  ((LocalCone.SemilatticeLocalCone.cone C I P h).naturality (homOfLE hIJ).op).symm.trans
    ((Category.id_comp _).trans (LocalCone.SemilatticeLocalCone.self C I P h))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeUpper.SemilatticeLocalConeUpper
