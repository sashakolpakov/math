import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne

/-! # Unit Hom Top Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections

noncomputable section

/-! Morphisms from the structure module are exactly actual global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

def moduleSectionsEquivTop {X : Scheme.{u}} (M : X.Modules) : M.sections ≃ Γ(M, ⊤) where
  toFun s := s.eval (op ⊤)
  invFun := AffineRankOne.globalSectionFamily M
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact s.property (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  right_inv x := by
    change M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x
    have h : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) :=
      Subsingleton.elim _ _
    rw [h, CategoryTheory.Functor.map_id]
    rfl

def unitHomTopSectionsEquiv {X : Scheme.{u}} (M : X.Modules) :
    (Invertible.Scheme.Modules.unitObj X ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (moduleSectionsEquivTop M)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections
