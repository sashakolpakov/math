import OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleRigidity

/-! # Etale Section Iso -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleSectionIso.Construction

noncomputable section

/-! # Completion: a section of a connected separated étale cover is its inverse -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- A connected separated étale cover with a section over a nonempty base is trivial. -/
theorem connected_etale_section_isIso {X Y : Scheme.{u}} [PreconnectedSpace X] [Nonempty Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    IsIso f := by
  have : PreconnectedSpace (Over.mk f).left := ‹PreconnectedSpace X›
  have : Nonempty (Over.mk (𝟙 Y)).left := ‹Nonempty Y›
  have : Etale (Over.mk f).hom := ‹Etale f›
  have : IsSeparated (Over.mk f).hom := ‹IsSeparated f›
  let g : Over.mk f ⟶ Over.mk f := Over.homMk (f ≫ s) (by simp [hs])
  let a : Over.mk (𝟙 Y) ⟶ Over.mk f := Over.homMk s hs
  have he : 𝟙 (Over.mk f) = g := EtaleRigidity.Construction.etale_hom_ext_of_nonempty _ _ a (by
    apply Over.OverMorphism.ext
    change s ≫ 𝟙 X = s ≫ (f ≫ s)
    rw [Category.comp_id, ← Category.assoc, hs, Category.id_comp])
  have hfs : f ≫ s = 𝟙 X := (congrArg (fun k => k.left) he).symm
  exact ⟨⟨s, hfs, hs⟩⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleSectionIso.Construction
