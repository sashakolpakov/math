import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

/-! # Sections Open Equality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsOpenEquality

noncomputable section

/-! Canonical transport between equal neighborhoods preserves
supported sections, their inclusion, and extension to global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}
  (O U V : Opens X) (h : U = V)

def iso :
    SectionsExcision.supported (D := D) U (U ⊓ O) inf_le_left ≅
      SectionsExcision.supported V (V ⊓ O) inf_le_left :=
  eqToIso (congrArg (fun W =>
    SectionsExcision.supported (D := D) W (W ⊓ O) inf_le_left) h)

theorem inclusion (F : Sheaf (Opens.grothendieckTopology X) D) :
    (iso O U V h).hom.app F ≫ (SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app F =
      (SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F ≫
        F.obj.map (eqToHom h.symm).op := by
  subst V
  change 𝟙 _ ≫ (SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F =
    (SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F ≫ F.obj.map (𝟙 (op U))
  erw [Category.id_comp, F.obj.map_id, Category.comp_id]

theorem extension (hU : U ⊔ O = ⊤) (hV : V ⊔ O = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) D) :
    (iso O U V h).hom.app F ≫ (SectionsExcision.extension O V hV).app F =
      (SectionsExcision.extension O U hU).app F := by
  subst V
  simp [iso]

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)

def complexIso := (NatIso.mapHomologicalComplex (iso (D := D) O U V h) (.up ℕ)).app K

theorem complex_extension (hU : U ⊔ O = ⊤) (hV : V ⊔ O = ⊤) :
    (complexIso O U V h K).hom ≫ SectionsExcision.extensionComplex O V hV K =
      SectionsExcision.extensionComplex O U hU K := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact extension O U V h hU hV (K.X n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsOpenEquality
