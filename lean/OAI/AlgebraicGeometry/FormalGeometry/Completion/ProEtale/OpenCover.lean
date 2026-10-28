import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover

/-! # Open Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover.Construction

noncomputable section

/-!
# Completion: ordinary open covers inside the actual pro-étale site

Every open cover of a site object is an actual covering family. This gives
the section equality and gluing rules used to identify the global torsor scheme.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X : Scheme.{u}} (U : X.ProEt) (V : U.left.OpenCover.{v})

/-- An open-cover member, with its actual structure map to the original base. -/
def proEtaleOpenCoverObject (i : V.I₀) : X.ProEt := Scheme.ProEt.mk (V.f i ≫ U.hom)

/-- The inclusion of the open-cover member in the original site object. -/
def proEtaleOpenCoverMap (i : V.I₀) : proEtaleOpenCoverObject U V i ⟶ U :=
  MorphismProperty.Over.homMk (V.f i) rfl

/-- The ordinary open cover generates an actual covering sieve. -/
theorem proEtaleOpenCover_cover :
    Sieve.generate (Presieve.ofArrows (proEtaleOpenCoverObject U V) (proEtaleOpenCoverMap U V)) ∈
      Scheme.ProEt.topology X U := by
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (proEtaleOpenCoverObject U V) (proEtaleOpenCoverMap U V)).map
    (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage U.left
  rw [Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ V.mem₀

/-- Sections of the actual sheaf are determined on an ordinary open cover. -/
theorem proEtaleOpenCover_section_ext (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (s t : F.obj.obj (op U))
    (h : ∀ i, F.obj.map (proEtaleOpenCoverMap U V i).op s =
      F.obj.map (proEtaleOpenCoverMap U V i).op t) : s = t := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  apply (hF.isSheafFor _ (proEtaleOpenCover_cover U V)).isSeparatedFor.ext
  intro W g hg
  cases hg with
  | mk i => exact h i

/-- Compatible sections on an ordinary open cover glue uniquely in the actual sheaf. -/
theorem proEtaleOpenCover_glue (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (s : ∀ i, F.obj.obj (op (proEtaleOpenCoverObject U V i)))
    (h : Presieve.Arrows.Compatible F.obj (proEtaleOpenCoverMap U V) s) :
    ∃! t : F.obj.obj (op U), ∀ i, F.obj.map (proEtaleOpenCoverMap U V i).op t = s i := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  exact (Presieve.isSheafFor_arrows_iff F.obj (proEtaleOpenCoverMap U V)).mp
    (hF.isSheafFor _ (proEtaleOpenCover_cover U V)) s h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover.Construction
