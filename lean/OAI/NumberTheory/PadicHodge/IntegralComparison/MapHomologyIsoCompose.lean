import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Map Homology Iso Compose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MapHomologyIsoCompose

noncomputable section

/-! The canonical homology comparison for a composite functor is
the composite of the canonical comparisons. This keeps scalar extension
and affine sections normalized on the original homology object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (S : ShortComplex C)
  [F.PreservesLeftHomologyOf S]

local instance : (F ⋙ G).PreservesLeftHomologyOf S :=
  HomologyPreservationCompose.left F G S

theorem mapped_cycles (h : S.LeftHomologyData) :
    (h.map (F ⋙ G)).cyclesIso.hom = ((h.map F).map G).cyclesIso.hom := by
  apply (cancel_mono (h.map (F ⋙ G)).i).mp
  exact (h.map (F ⋙ G)).cyclesIso_hom_comp_i.trans
    ((h.map F).map G).cyclesIso_hom_comp_i.symm

theorem mapped_homology (h : S.LeftHomologyData) :
    (h.map (F ⋙ G)).homologyIso.hom = ((h.map F).map G).homologyIso.hom := by
  apply (cancel_epi ((S.map F).map G).homologyπ).mp
  exact (h.map (F ⋙ G)).homologyπ_comp_homologyIso_hom.trans
    ((congrArg (fun k => k ≫ (h.map (F ⋙ G)).π) (mapped_cycles F G S h)).trans
      ((h.map F).map G).homologyπ_comp_homologyIso_hom.symm)

theorem iso_comp :
    S.mapHomologyIso (F ⋙ G) =
      (S.map F).mapHomologyIso G ≪≫ G.mapIso (S.mapHomologyIso F) := by
  rw [(S.homologyData.left.map F).mapHomologyIso_eq G]
  apply Iso.ext
  change (S.homologyData.left.map (F ⋙ G)).homologyIso.hom =
    (((S.homologyData.left.map F).map G).homologyIso.hom ≫
      G.map (S.homologyData.left.map F).homologyIso.inv) ≫
        G.map (S.homologyData.left.map F).homologyIso.hom
  rw [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id]
  erw [Category.comp_id]
  exact mapped_homology F G S S.homologyData.left

@[reassoc]
theorem hom_comp :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom :=
  congrArg Iso.hom (iso_comp F G S)

@[reassoc]
theorem inv_comp :
    (S.mapHomologyIso (F ⋙ G)).inv =
      G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv :=
  congrArg Iso.inv (iso_comp F G S)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MapHomologyIsoCompose
