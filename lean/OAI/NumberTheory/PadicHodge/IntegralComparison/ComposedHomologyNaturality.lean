import OAI.NumberTheory.PadicHodge.IntegralComparison.MapHomologyIsoCompose

/-! # Composed Homology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ComposedHomologyNaturality

noncomputable section

/-! A natural comparison to a composite functor commutes with the
original homology isomorphisms, including the intermediate evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (τ : H ⟶ F ⋙ G) (S : ShortComplex C)
  [F.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
  [H.PreservesLeftHomologyOf S] [H.PreservesRightHomologyOf S]

local instance : (F ⋙ G).PreservesLeftHomologyOf S := HomologyPreservationCompose.left F G S
local instance : (F ⋙ G).PreservesRightHomologyOf S := HomologyPreservationCompose.right F G S

theorem square :
    τ.app S.homology ≫ G.map (S.mapHomologyIso F).inv =
      (S.mapHomologyIso H).inv ≫ ShortComplex.homologyMap (S.mapNatTrans τ) ≫
        ((S.map F).mapHomologyIso G).hom := by
  rw [τ.app_homology S, MapHomologyIsoCompose.hom_comp F G S]
  simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ComposedHomologyNaturality
