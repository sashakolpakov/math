import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Homology Functor Coherence -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomologyFunctorCoherence

noncomputable section

section

/-! # Coherence of the canonical homology comparison under composition of exact functors -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem homologyComparison_cycles (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq h F,
    ShortComplex.LeftHomologyData.mapCyclesIso_eq h F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [Category.assoc]
  change (h.map F).cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  rw [← Functor.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
    Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem cyclesComparison_comp (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesLeftHomologyOf S]
    [G.PreservesLeftHomologyOf (S.map F)] [(F ⋙ G).PreservesLeftHomologyOf S]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    (S.mapCyclesIso (F ⋙ G)).hom =
      ((S.map F).mapCyclesIso G).hom ≫ G.map (S.mapCyclesIso F).hom := by
  apply (cancel_mono (G.map (F.map S.iCycles))).mp
  simp only [Category.assoc, ← G.map_comp,
    ShortComplex.mapCyclesIso_hom_iCycles]
  change (S.mapCyclesIso (F ⋙ G)).hom ≫ (F ⋙ G).map S.iCycles = _
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem homologyComparison_comp (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesLeftHomologyOf S]
    [G.PreservesLeftHomologyOf (S.map F)] [(F ⋙ G).PreservesLeftHomologyOf S]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  apply (cancel_epi ((S.map (F ⋙ G)).homologyπ)).mp
  have hG : (S.map (F ⋙ G)).homologyπ ≫ ((S.map F).mapHomologyIso G).hom =
      ((S.map F).mapCyclesIso G).hom ≫ G.map (S.map F).homologyπ := by
    exact homologyComparison_cycles (S.map F) G
  have hF := homologyComparison_cycles S F
  have hH := homologyComparison_cycles S (F ⋙ G)
  have hcy := cyclesComparison_comp S F G
  rw [hH, ← Category.assoc, hG, Category.assoc, ← G.map_comp,
    hF, G.map_comp, ← Category.assoc, ← hcy]
  rfl

end

/-! # The canonical homology comparison respects identities and natural transformations -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem homologyComparison_id (S : ShortComplex C) :
    (S.mapHomologyIso (𝟭 C)).hom = 𝟙 S.homology := by
  have hc : (S.mapCyclesIso (𝟭 C)).hom = 𝟙 S.cycles := by
    dsimp only [ShortComplex.map, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map]
    apply (cancel_mono S.iCycles).mp
    rw [Category.id_comp]
    change (S.mapCyclesIso (𝟭 C)).hom ≫ (𝟭 C).map S.iCycles = (S.map (𝟭 C)).iCycles
    exact ShortComplex.mapCyclesIso_hom_iCycles S (𝟭 C)
  apply (cancel_epi S.homologyπ).mp
  dsimp only [ShortComplex.map, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map]
  have h := homologyComparison_cycles S (𝟭 C)
  dsimp only [ShortComplex.map, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map] at h
  rw [Category.comp_id]
  change (S.map (𝟭 C)).homologyπ ≫ (S.mapHomologyIso (𝟭 C)).hom = _
  simpa only [hc, CategoryTheory.Functor.id_map, Category.id_comp] using! h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem homologyComparison_natTrans (S : ShortComplex C) (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.PreservesLeftHomologyOf S]
    [G.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [G.PreservesRightHomologyOf S] (τ : F ⟶ G) :
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology := by
  rw [ShortComplex.homologyMap_mapNatTrans, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomologyFunctorCoherence
