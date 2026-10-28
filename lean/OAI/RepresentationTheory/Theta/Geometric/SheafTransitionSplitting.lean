import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Sheaf Transition Splitting -/

namespace OAI.RepresentationTheory.Theta.Geometric.SheafTransitionSplitting

noncomputable section

/-! Splitting the actual transition cocycle of local lifts gives a
global lift in a short exact sequence of abelian sheaves. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : S.ShortExact) {t : S.X₃.obj.obj (op (⊤ : Opens X))}
    (l : AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t)

theorem exists_globalLift_of_transition_split {ι : Type} (a : ι → X)
    (hcover : (⊤ : Opens X) ≤ ⨆ i, l.domain (a i))
    (r : ∀ i, S.X₁.obj.obj (op (l.domain (a i))))
    (hr : ∀ i j, l.transition hS (a i) (a j) =
      AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ inf_le_right (r j) -
        AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ inf_le_left (r i)) :
    ∃ s : S.X₂.obj.obj (op (⊤ : Opens X)), S.g.hom.app (op ⊤) s = t := by
  let U := fun i => l.domain (a i)
  let b := fun i => l.section_ (a i) - S.f.hom.app (op (U i)) (r i)
  have hb : TopCat.Presheaf.IsCompatible S.X₂.obj U b := by
    intro i j
    have h := congrArg (S.f.hom.app (op (U i ⊓ U j))) (hr i j)
    rw [l.transition_map, map_sub, AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict,
      AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict] at h
    change AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (l.section_ (a j)) -
      AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (l.section_ (a i)) =
        AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (S.f.hom.app (op (U j)) (r j)) -
          AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (S.f.hom.app (op (U i)) (r i)) at h
    change AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_left (b i) =
      AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ inf_le_right (b j)
    dsimp only [b]
    rw [map_sub, map_sub]
    exact (sub_eq_sub_iff_sub_eq_sub.mp h).symm
  obtain ⟨s, hs, _⟩ := S.X₂.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover b hb
  refine ⟨s, ?_⟩
  apply S.X₃.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hcover
  intro i
  change AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top (S.g.hom.app (op ⊤) s) =
    AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top t
  rw [← AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict]
  have hsi : AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ le_top s = b i := hs i
  rw [hsi]
  dsimp only [b]
  rw [map_sub, l.image]
  have hz : S.g.hom.app (op (U i)) (S.f.hom.app (op (U i)) (r i)) = 0 := by
    change (S.f ≫ S.g).hom.app (op (U i)) (r i) = 0
    rw [S.zero]
    rfl
  rw [hz, sub_zero]
  rfl

theorem injectiveCokernelBoundary_image_zero (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (s : (AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F).X₂.obj.obj (op (⊤ : Opens X))) :
    AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary F
      ((AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F).g.hom.app (op ⊤) s) = 0 := by
  let S := AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F
  change ((CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm
    (S.g.hom.app (op (⊤ : Opens X)) s)).comp
      (AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact F).extClass (rfl : 0 + 1 = 1) = 0
  rw [← CategoryTheory.Sheaf.H.equiv₀_symm_naturality]
  change (((CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm s).comp
    (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero 0)).comp
      (AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact F).extClass (rfl : 0 + 1 = 1) = 0
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    (AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact F).comp_extClass,
    CategoryTheory.Abelian.Ext.comp_zero]

end

end OAI.RepresentationTheory.Theta.Geometric.SheafTransitionSplitting
