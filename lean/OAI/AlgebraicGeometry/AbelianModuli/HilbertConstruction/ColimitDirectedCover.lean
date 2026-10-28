import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Colimit Directed Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ColimitDirectedCover

noncomputable section

/-! The canonical cover of a locally directed scheme colimit has the corresponding directed cover structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

variable {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
variable (F : J ⥤ Scheme.{u}) [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h)]
variable [(F ⋙ Scheme.forget).IsLocallyDirected]

abbrev colimitDiagramCover : (colimit F).OpenCover where
  I₀ := J
  X := F.obj
  f := colimit.ι F
  mem₀ := (Scheme.IsLocallyDirected.openCover F).mem₀

instance colimitDiagramCover_locallyDirected : (colimitDiagramCover F).LocallyDirected where
  trans := F.map
  trans_id := F.map_id
  trans_comp := F.map_comp
  w := colimit.w F
  directed {i j} x := by
    let xi := pullback.fst (colimit.ι F i) (colimit.ι F j) x
    let xj := pullback.snd (colimit.ι F i) (colimit.ι F j) x
    have hx : colimit.ι F i xi = colimit.ι F j xj :=
      congrArg (fun f => f x) (pullback.condition (f := colimit.ι F i) (g := colimit.ι F j))
    obtain ⟨k, fi, fj, y, hi, _⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hx
    refine ⟨k, fi, fj, y, ?_⟩
    have : IsOpenImmersion (colimit.ι F j) := (colimitDiagramCover F).map_prop j
    apply (pullback.fst (colimit.ι F i) (colimit.ι F j)).injective
    simpa only [← Scheme.Hom.comp_apply, pullback.lift_fst] using hi
  property_trans := fun h => inferInstanceAs (IsOpenImmersion (F.map h))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ColimitDirectedCover
