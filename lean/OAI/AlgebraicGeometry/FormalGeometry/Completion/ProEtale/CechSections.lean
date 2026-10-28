import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover

/-! # Cech Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction

noncomputable section

/-!
# Completion: descent of sections from an actual geometric overlap

The ordinary scheme pullback suffices to check the single-cover sheaf
condition, since its universal morphisms are also morphisms of the site.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {X : Scheme.{u}} {U V D : X.ProEt}

/-- Agreement on the actual geometric overlap descends sections uniquely. -/
theorem proEtaleSheaf_descend_section_of_isPullback
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (f : U ⟶ V) [Surjective f.left] [QuasiCompact f.left]
    (a b : D ⟶ U) (h : IsPullback a.left b.left f.left f.left)
    (s : F.obj.obj (op U)) (hs : F.obj.map a.op s = F.obj.map b.op s) :
    ∃! t : F.obj.obj (op V), F.obj.map f.op t = s := by
  apply SingleCover.Construction.proEtaleSheaf_descend_section F f s
  intro W p q hpq
  have hw : p.left ≫ f.left = q.left ≫ f.left :=
    congrArg (fun k : W ⟶ V => k.left) hpq
  let l : W ⟶ D := MorphismProperty.Over.homMk (h.lift p.left q.left hw) (by
    rw [← MorphismProperty.Over.w a, ← Category.assoc, h.lift_fst]
    exact MorphismProperty.Over.w p)
  have hp : l ≫ a = p := MorphismProperty.Over.Hom.ext (h.lift_fst _ _ _)
  have hq : l ≫ b = q := MorphismProperty.Over.Hom.ext (h.lift_snd _ _ _)
  rw [← hp, ← hq, op_comp, op_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  change F.obj.map l.op (F.obj.map a.op s) = F.obj.map l.op (F.obj.map b.op s)
  rw [hs]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.CechSections.Construction
