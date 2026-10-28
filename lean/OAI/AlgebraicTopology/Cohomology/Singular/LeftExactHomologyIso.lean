import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomology

/-! # Left Exact Homology Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso

noncomputable section

/-!
# Agreement with the right-homology comparison

When a left exact functor additionally preserves the right homology data of
one short complex, its canonical comparison agrees with mathlib's comparison
isomorphism. This does not require the functor to be exact on other complexes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]
  (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
  [F.PreservesRightHomologyOf S]

@[reassoc]
theorem pOpcycles_mapOpcyclesIso_hom :
    (S.map F).pOpcycles ≫ (S.mapOpcyclesIso F).hom = F.map S.pOpcycles :=
  (S.rightHomologyData.map F).pOpcycles_comp_opcyclesIso_hom

@[reassoc]
theorem mapHomologyIso'_hom_map_homologyι :
    (S.mapHomologyIso' F).hom ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ (S.mapOpcyclesIso F).hom := by
  let h := S.rightHomologyData
  rw [h.mapHomologyIso'_eq F, h.mapOpcyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← F.map_comp, h.homologyIso_inv_comp_homologyι, F.map_comp, ← Category.assoc]
  have hι : (h.map F).homologyIso.hom ≫ F.map h.ι =
      (S.map F).homologyι ≫ (h.map F).opcyclesIso.hom :=
    (h.map F).homologyIso_hom_comp_ι
  rw [hι, Category.assoc]

variable [PreservesFiniteLimits F]

/-- The canonical left-exact comparison is the existing right-homology
isomorphism whenever that individual homology datum is preserved. -/
theorem leftExactHomologyComparison_eq_mapHomologyIso' :
    LeftExactHomology.leftExactHomologyComparison S F = (S.mapHomologyIso' F).hom := by
  apply (cancel_mono (F.map S.homologyι)).mp
  apply (cancel_epi (S.map F).homologyπ).mp
  calc
    (S.map F).homologyπ ≫ LeftExactHomology.leftExactHomologyComparison S F ≫ F.map S.homologyι =
        (S.map F).iCycles ≫ F.map S.pOpcycles := by
      rw [← Category.assoc, LeftExactHomology.homologyπ_leftExactHomologyComparison, Category.assoc,
        ← F.map_comp, ShortComplex.homology_π_ι, F.map_comp, ← Category.assoc,
        LeftExactHomology.leftExactCyclesIso_hom_iCycles]
    _ = (S.map F).homologyπ ≫ (S.mapHomologyIso' F).hom ≫ F.map S.homologyι := by
      rw [mapHomologyIso'_hom_map_homologyι, ← Category.assoc,
        ShortComplex.homology_π_ι, Category.assoc, pOpcycles_mapOpcyclesIso_hom]

end

end OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso
