import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

/-! # Zero Complement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplement

noncomputable section

/-! For a sheaf vanishing on the complement of its support, its
global sections are recovered by the actual supported extension
from any open neighborhood of that support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}

theorem inclusion_isIso (U V : Opens X) (h : V ≤ U)
    (F : Sheaf (Opens.grothendieckTopology X) D) (hV : IsZero (F.obj.obj (op V))) :
    IsIso ((SectionsExcision.inclusion U V h).app F) := by
  change IsIso (kernel.ι ((SectionsExcision.restriction U V h).app F))
  have hz : (SectionsExcision.restriction U V h).app F = 0 := hV.eq_zero_of_tgt _
  rw [hz]
  infer_instance

variable (O U : Opens X) (hcover : U ⊔ O = ⊤)
  (F : Sheaf (Opens.grothendieckTopology X) D) (hO : IsZero (F.obj.obj (op O)))

def globalIso := @asIso _ _ _ _ ((SectionsExcision.inclusion ⊤ O le_top).app F)
  (inclusion_isIso ⊤ O le_top F hO)

def lift : (SectionsExcision.sections ⊤).obj F ⟶ (SectionsExcision.supported U (U ⊓ O) inf_le_left).obj F :=
  (globalIso O F hO).inv ≫ (SectionsExcision.excision O U).app F

theorem lift_inclusion : lift O U F hO ≫ (SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F =
    (SectionsExcision.restriction ⊤ U le_top).app F := by
  rw [lift, Category.assoc, SectionsExcision.excision_inclusion]
  exact (globalIso O F hO).inv_hom_id_assoc _

theorem lift_extension : lift O U F hO ≫ (SectionsExcision.extension O U hcover).app F = 𝟙 _ := by
  change ((globalIso O F hO).inv ≫ ((SectionsExcision.excisionIso O U hcover).app F).hom) ≫
    (((SectionsExcision.excisionIso O U hcover).app F).inv ≫ (SectionsExcision.inclusion ⊤ O le_top).app F) = 𝟙 _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (globalIso O F hO).inv_hom_id

variable (hUO : IsZero (F.obj.obj (op (U ⊓ O))))

def localIso := @asIso _ _ _ _ ((SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F)
  (inclusion_isIso U (U ⊓ O) inf_le_left F hUO)

theorem localIso_hom : (localIso O U F hUO).hom =
    (SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F := rfl

theorem lift_eq_local : lift O U F hO =
    (SectionsExcision.restriction ⊤ U le_top).app F ≫ (localIso O U F hUO).inv := by
  apply (cancel_mono (localIso O U F hUO).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [localIso_hom]
  exact lift_inclusion O U F hO

include hcover hO hUO in
theorem restriction_isIso : IsIso ((SectionsExcision.restriction ⊤ U le_top).app F) := by
  let : IsIso ((SectionsExcision.excision O U).app F) := SectionsExcision.excision_isIso O U hcover F
  let : IsIso ((SectionsExcision.inclusion U (U ⊓ O) inf_le_left).app F) := inclusion_isIso U (U ⊓ O) inf_le_left F hUO
  rw [← lift_inclusion O U F hO]
  dsimp only [lift]
  infer_instance

include hO in
theorem local_extension :
    ((SectionsExcision.restriction ⊤ U le_top).app F ≫ (localIso O U F hUO).inv) ≫
      (SectionsExcision.extension O U hcover).app F = 𝟙 _ := by
  rw [← lift_eq_local O U F hO hUO, lift_extension]

variable {G : Sheaf (Opens.grothendieckTopology X) D} (a : F ⟶ G)

theorem map_extension :
    (lift O U F hO ≫ (SectionsExcision.supported U (U ⊓ O) inf_le_left).map a) ≫
      (SectionsExcision.extension O U hcover).app G = (SectionsExcision.sections ⊤).map a := by
  rw [Category.assoc, (SectionsExcision.extension O U hcover).naturality a,
    ← Category.assoc, lift_extension, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplement
