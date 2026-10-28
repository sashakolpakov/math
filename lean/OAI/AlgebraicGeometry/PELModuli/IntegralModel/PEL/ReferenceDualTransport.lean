import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ReferenceDualProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointProjection

/-! # Reference Dual Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

/-! The transport induced by an actual reference PEL family preserves
its dual projection, as an equality of actual scheme maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ} {S X T : Scheme.{0}}
    {A : Has.PolarizedActionData E g δ N X} (B : Has.PolarizedActionData E g δ N S)
    (u : X ⟶ S) (a : Iso.PolarizedActionIso (B.pullback u) A)
    (f h : T ⟶ X) (w : f ≫ u = h ≫ u)

def Iso.PolarizedActionIso.referenceTransport : Iso.PolarizedActionIso (A.pullback f) (A.pullback h) :=
  ((Iso.PolarizedActionIso.referencePullbackComparison B u a f).trans (Iso.PolarizedActionIso.pullbackCongr B _ _ w)).trans
    (Iso.PolarizedActionIso.referencePullbackComparison B u a h).symm

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.referenceTransport_dual_projection :
    (Iso.PolarizedActionIso.referenceTransport B u a f h w).polarized.dual.hom.left ≫
        pullback.fst A.polarized.dual.abelian.scheme.hom h ≫ Iso.PolarizedActionIso.referenceDualProjection B u a =
      pullback.fst A.polarized.dual.abelian.scheme.hom f ≫ Iso.PolarizedActionIso.referenceDualProjection B u a := by
  let af := Iso.PolarizedActionIso.referencePullbackComparison B u a f
  let ah := Iso.PolarizedActionIso.referencePullbackComparison B u a h
  let ec := Iso.PolarizedActionIso.pullbackCongr B (f ≫ u) (h ≫ u) w
  have hh : ah.polarized.dual.inv.left ≫
      (pullback.fst A.polarized.dual.abelian.scheme.hom h ≫ Iso.PolarizedActionIso.referenceDualProjection B u a) =
        pullback.fst B.polarized.dual.abelian.scheme.hom (h ≫ u) := by
    exact (congrArg (fun k => ah.polarized.dual.inv.left ≫ k)
      (Iso.PolarizedActionIso.referencePullbackComparison_dual_fst B u a h).symm).trans
        (Over.inv_left_hom_left_assoc ah.polarized.dual _)
  change ((af.polarized.dual.hom.left ≫ ec.polarized.dual.hom.left) ≫
      ah.polarized.dual.inv.left) ≫ _ ≫ _ = _
  rw [Category.assoc, Category.assoc, hh, Iso.PolarizedActionIso.pullbackCongr_dual_fst]
  exact Iso.PolarizedActionIso.referencePullbackComparison_dual_fst B u a f

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.referenceTransport_dual_point
    (x : T ⟶ A.polarized.dual.abelian.scheme.left)
    (hx : x ≫ A.polarized.dual.abelian.scheme.hom = f) :
    Family.PointBaseChange.FamilyPointTransport.transport A.polarized.dual.abelian.scheme f h
      (Iso.PolarizedActionIso.referenceTransport B u a f h w).polarized.dual x hx ≫ Iso.PolarizedActionIso.referenceDualProjection B u a =
        x ≫ Iso.PolarizedActionIso.referenceDualProjection B u a :=
  Family.PointProjection.FamilyPointTransport.transport_projection _ _ _ _ _
    (Iso.PolarizedActionIso.referenceTransport_dual_projection B u a f h w) x hx

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL
