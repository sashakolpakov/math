import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplement
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Zero Complement Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplementComplex

noncomputable section

/-! A complex vanishing on the complement has a canonical supported
lift from every neighborhood, and its extension is the original global
complex map. This identity also holds on genuine cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}
  (O U : Opens X) (hcover : U ⊔ O = ⊤)
  (L : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)

def globalInclusion := (NatTrans.mapHomologicalComplex (SectionsExcision.inclusion ⊤ O le_top) (.up ℕ)).app L
def localInclusion := (NatTrans.mapHomologicalComplex (SectionsExcision.inclusion U (U ⊓ O) inf_le_left) (.up ℕ)).app L
def restrictionMap := (NatTrans.mapHomologicalComplex (SectionsExcision.restriction ⊤ U le_top) (.up ℕ)).app L
def excisionMap := (NatTrans.mapHomologicalComplex (SectionsExcision.excision O U) (.up ℕ)).app L

theorem excision_inclusion : excisionMap O U L ≫ localInclusion O U L =
    globalInclusion O L ≫ restrictionMap U L := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact SectionsExcision.excision_inclusion O U (L.X q)

variable (hO : ∀ q, IsZero ((L.X q).obj.obj (op O)))

include hO in
theorem globalInclusion_isIso : IsIso (globalInclusion O L) := by
  let : ∀ q, IsIso ((globalInclusion O L).f q) := fun q =>
    ZeroComplement.inclusion_isIso ⊤ O le_top (L.X q) (hO q)
  exact HomologicalComplex.Hom.isIso_of_components _

def globalIso := @asIso _ _ _ _ (globalInclusion O L) (globalInclusion_isIso O L hO)

def lift := (globalIso O L hO).inv ≫ excisionMap O U L

theorem lift_inclusion : lift O U L hO ≫ localInclusion O U L = restrictionMap U L := by
  rw [lift, Category.assoc, excision_inclusion]
  exact (globalIso O L hO).inv_hom_id_assoc _

theorem lift_extension : lift O U L hO ≫ SectionsExcision.extensionComplex O U hcover L = 𝟙 _ := by
  let e := (NatIso.mapHomologicalComplex (SectionsExcision.excisionIso (D := D) O U hcover) (.up ℕ)).app L
  change ((globalIso O L hO).inv ≫ e.hom) ≫ (e.inv ≫ globalInclusion O L) = 𝟙 _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (globalIso O L hO).inv_hom_id

variable {M : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ} (a : L ⟶ M)

theorem map_extension :
    (lift O U L hO ≫ ((SectionsExcision.supported U (U ⊓ O) inf_le_left).mapHomologicalComplex (.up ℕ)).map a) ≫
      SectionsExcision.extensionComplex O U hcover M = ((SectionsExcision.sections ⊤).mapHomologicalComplex (.up ℕ)).map a := by
  have h := (NatTrans.mapHomologicalComplex (SectionsExcision.extension (D := D) O U hcover) (.up ℕ)).naturality a
  change ((SectionsExcision.supported U (U ⊓ O) inf_le_left).mapHomologicalComplex (.up ℕ)).map a ≫
    SectionsExcision.extensionComplex O U hcover M = SectionsExcision.extensionComplex O U hcover L ≫
      ((SectionsExcision.sections ⊤).mapHomologicalComplex (.up ℕ)).map a at h
  rw [Category.assoc, h, ← Category.assoc, lift_extension, Category.id_comp]

theorem homology_extension (i : ℕ) :
    HomologicalComplex.homologyMap (lift O U L hO) i ≫
      HomologicalComplex.homologyMap (SectionsExcision.extensionComplex O U hcover L) i = 𝟙 _ := by
  simpa only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] using
    congrArg (fun f => HomologicalComplex.homologyMap f i) (lift_extension O U hcover L hO)

theorem homology_map_extension (i : ℕ) :
    (HomologicalComplex.homologyMap (lift O U L hO) i ≫
      HomologicalComplex.homologyMap
        (((SectionsExcision.supported U (U ⊓ O) inf_le_left).mapHomologicalComplex (.up ℕ)).map a) i) ≫
      HomologicalComplex.homologyMap (SectionsExcision.extensionComplex O U hcover M) i =
        HomologicalComplex.homologyMap (((SectionsExcision.sections ⊤).mapHomologicalComplex (.up ℕ)).map a) i := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun f => HomologicalComplex.homologyMap f i) (map_extension O U hcover L hO a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplementComplex
