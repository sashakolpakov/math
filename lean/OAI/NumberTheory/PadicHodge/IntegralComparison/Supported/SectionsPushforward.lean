import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
import Mathlib.Topology.Sheaves.Sheaf

/-! # Sections Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsPushforward

noncomputable section

/-! Supported sections of a pushed sheaf are the actual sections over
inverse images. Their extension to global sections is unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D]
  {X Y : TopCat.{w}} (f : Y ⟶ X)

abbrev preimage : Opens X ⥤ Opens Y := Opens.map f

def pushforward : Sheaf (Opens.grothendieckTopology Y) D ⥤
    Sheaf (Opens.grothendieckTopology X) D :=
  (preimage f).sheafPushforwardContinuous D
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

instance pushforward_additive : (pushforward (D := D) f).Additive where
  map_add := by intros; rfl

def sectionsIso (U : Opens X) :
    pushforward (D := D) f ⋙ SectionsExcision.sections U ≅
      SectionsExcision.sections ((preimage f).obj U) := Iso.refl _

def supportedIso (O U : Opens X) :
    pushforward (D := D) f ⋙ SectionsExcision.supported U (U ⊓ O) inf_le_left ≅
      SectionsExcision.supported ((preimage f).obj U)
        ((preimage f).obj U ⊓ (preimage f).obj O) inf_le_left := Iso.refl _

theorem preimage_cover (O U : Opens X) (hcover : U ⊔ O = ⊤) :
    (preimage f).obj U ⊔ (preimage f).obj O = ⊤ := by
  change (preimage f).obj (U ⊔ O) = (preimage f).obj ⊤
  rw [hcover]

theorem excision (O U : Opens X) (N : Sheaf (Opens.grothendieckTopology Y) D) :
    (SectionsExcision.excision O U).app ((pushforward f).obj N) =
    (SectionsExcision.excision ((preimage f).obj O) ((preimage f).obj U)).app N := rfl

theorem extension (O U : Opens X) (hcover : U ⊔ O = ⊤)
    (N : Sheaf (Opens.grothendieckTopology Y) D) :
    (SectionsExcision.extension O U hcover).app ((pushforward f).obj N) =
    (SectionsExcision.extension ((preimage f).obj O) ((preimage f).obj U)
      (preimage_cover f O U hcover)).app N := rfl

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) D) ℕ)

abbrev pushed := ((pushforward (D := D) f).mapHomologicalComplex (.up ℕ)).obj K

def sourceIso (O U : Opens X) :
    ((SectionsExcision.supported U (U ⊓ O) inf_le_left).mapHomologicalComplex (.up ℕ)).obj
      (pushed f K) ≅
    ((SectionsExcision.supported ((preimage f).obj U)
      ((preimage f).obj U ⊓ (preimage f).obj O) inf_le_left).mapHomologicalComplex (.up ℕ)).obj K :=
  Iso.refl _

def globalIso :
    ((SectionsExcision.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj
      (pushed f K) ≅
    ((SectionsExcision.sections (⊤ : Opens Y)).mapHomologicalComplex (.up ℕ)).obj K :=
  Iso.refl _

theorem complex_extension (O U : Opens X) (hcover : U ⊔ O = ⊤) :
    SectionsExcision.extensionComplex O U hcover (pushed f K) ≫ (globalIso f K).hom =
    (sourceIso f K O U).hom ≫
      SectionsExcision.extensionComplex ((preimage f).obj O) ((preimage f).obj U)
        (preimage_cover f O U hcover) K := by
  apply HomologicalComplex.Hom.ext
  funext q
  change (SectionsExcision.extension O U hcover).app ((pushforward f).obj (K.X q)) ≫ 𝟙 _ =
    𝟙 _ ≫ (SectionsExcision.extension ((preimage f).obj O) ((preimage f).obj U)
      (preimage_cover f O U hcover)).app (K.X q)
  rw [Category.comp_id, Category.id_comp, extension]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsPushforward
