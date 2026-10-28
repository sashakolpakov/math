import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

/-! # Sections Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestriction

noncomputable section

/-! Restriction between two neighborhoods of the same support is the
literal map of section kernels. It commutes with extension to global
sections, on sheaves, complexes, and cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

def map (O U V : Opens X) (h : V ≤ U) :
    SectionsExcision.supported (D := D) U (U ⊓ O) inf_le_left ⟶ SectionsExcision.supported V (V ⊓ O) inf_le_left where
  app F := kernel.map _ _ ((SectionsExcision.restriction U V h).app F)
    ((SectionsExcision.restriction (U ⊓ O) (V ⊓ O) (inf_le_inf_right O h)).app F) (by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1)
  naturality F G f := by
    apply (cancel_mono (kernel.ι ((SectionsExcision.restriction V (V ⊓ O) inf_le_left).app G))).mp
    simpa only [SectionsExcision.supported, kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc] using
      congrArg (fun a => kernel.ι ((SectionsExcision.restriction U (U ⊓ O) inf_le_left).app F) ≫ a)
        ((SectionsExcision.restriction U V h).naturality f)

theorem inclusion_square (O U V : Opens X) (h : V ≤ U)
    (F : Sheaf (Opens.grothendieckTopology X) D) :
    (SectionsRestriction.map O U V h).app F ≫ (SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app F =
      (SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F ≫ (SectionsExcision.restriction U V h).app F :=
  kernel.lift_ι _ _ _

theorem excision_square (O U V : Opens X) (h : V ≤ U) :
    SectionsExcision.excision (D := D) O U ≫ SectionsRestriction.map O U V h = SectionsExcision.excision O V := by
  apply NatTrans.ext
  funext F
  apply (cancel_mono (kernel.ι ((SectionsExcision.restriction V (V ⊓ O) inf_le_left).app F))).mp
  change ((SectionsExcision.excision O U).app F ≫ (SectionsRestriction.map O U V h).app F) ≫
      (SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app F =
    (SectionsExcision.excision O V).app F ≫ (SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app F
  rw [Category.assoc, inclusion_square, ← Category.assoc, SectionsExcision.excision_inclusion,
    SectionsExcision.excision_inclusion, Category.assoc]
  change (SectionsExcision.inclusion ⊤ O le_top).app F ≫ (F.obj.map _ ≫ F.obj.map _) =
    (SectionsExcision.inclusion ⊤ O le_top).app F ≫ F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

theorem cover (O U V : Opens X) (h : V ≤ U) (hV : V ⊔ O = ⊤) : U ⊔ O = ⊤ := by
  apply top_unique
  rw [← hV]
  exact sup_le_sup_right h O

theorem excision_extension (O U : Opens X) (hU : U ⊔ O = ⊤) :
    SectionsExcision.excision (D := D) O U ≫ SectionsExcision.extension O U hU = SectionsExcision.inclusion ⊤ O le_top := by
  change (SectionsExcision.excisionIso O U hU).hom ≫ (SectionsExcision.excisionIso O U hU).inv ≫ SectionsExcision.inclusion ⊤ O le_top = _
  rw [Iso.hom_inv_id_assoc]

theorem extension_square (O U V : Opens X) (h : V ≤ U)
    (hU : U ⊔ O = ⊤) (hV : V ⊔ O = ⊤) :
    SectionsRestriction.map (D := D) O U V h ≫ SectionsExcision.extension O V hV = SectionsExcision.extension O U hU := by
  apply (cancel_epi (SectionsExcision.excisionIso (D := D) O U hU).hom).mp
  change SectionsExcision.excision O U ≫ (SectionsRestriction.map O U V h ≫ SectionsExcision.extension O V hV) = SectionsExcision.excision O U ≫ SectionsExcision.extension O U hU
  rw [← Category.assoc, excision_square, excision_extension, excision_extension]

def complex (O U V : Opens X) (h : V ≤ U)
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ) :=
  (NatTrans.mapHomologicalComplex (SectionsRestriction.map O U V h) (.up ℕ)).app K

theorem complex_extension (O U V : Opens X) (h : V ≤ U)
    (hU : U ⊔ O = ⊤) (hV : V ⊔ O = ⊤)
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ) :
    complex O U V h K ≫ SectionsExcision.extensionComplex O V hV K = SectionsExcision.extensionComplex O U hU K := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun a => a.app (K.X n)) (extension_square (D := D) O U V h hU hV)

theorem homology_extension (O U V : Opens X) (h : V ≤ U)
    (hU : U ⊔ O = ⊤) (hV : V ⊔ O = ⊤)
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (complex O U V h K) n ≫
        HomologicalComplex.homologyMap (SectionsExcision.extensionComplex O V hV K) n =
      HomologicalComplex.homologyMap (SectionsExcision.extensionComplex O U hU K) n := by
  rw [← HomologicalComplex.homologyMap_comp, complex_extension]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsRestriction
