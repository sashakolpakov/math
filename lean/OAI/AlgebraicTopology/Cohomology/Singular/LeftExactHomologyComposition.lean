import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyIso

/-! # Left Exact Homology Composition -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

noncomputable section

/-!
# Composition of canonical left-exact homology comparisons

The canonical comparison through two left exact functors is the composite
of their canonical comparisons. When the relevant functor is exact, this
comparison is the usual homology-preservation isomorphism. These identities
keep the maps obtained by taking actual section germs compatible with the
canonical isomorphisms for stalk homology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]

local instance : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

/-- The genuine cycle-preservation maps compose as the functors do. -/
theorem leftExactCyclesIso_comp_hom :
    (LeftExactHomology.leftExactCyclesIso (S.map F) G).hom ≫ G.map (LeftExactHomology.leftExactCyclesIso S F).hom =
      (LeftExactHomology.leftExactCyclesIso S (F ⋙ G)).hom := by
  apply (cancel_mono ((F ⋙ G).map S.iCycles)).mp
  change ((LeftExactHomology.leftExactCyclesIso (S.map F) G).hom ≫ G.map (LeftExactHomology.leftExactCyclesIso S F).hom) ≫
      G.map (F.map S.iCycles) = _
  rw [Category.assoc, ← G.map_comp, LeftExactHomology.leftExactCyclesIso_hom_iCycles,
    LeftExactHomology.leftExactCyclesIso_hom_iCycles, LeftExactHomology.leftExactCyclesIso_hom_iCycles]
  rfl

/-- Canonical homology comparisons for left exact functors compose. -/
theorem leftExactHomologyComparison_comp :
    LeftExactHomology.leftExactHomologyComparison (S.map F) G ≫ G.map (LeftExactHomology.leftExactHomologyComparison S F) =
      LeftExactHomology.leftExactHomologyComparison S (F ⋙ G) := by
  apply (cancel_epi ((S.map F).map G).homologyπ).mp
  calc
    _ = (LeftExactHomology.leftExactCyclesIso (S.map F) G).hom ≫
        G.map (S.map F).homologyπ ≫ G.map (LeftExactHomology.leftExactHomologyComparison S F) := by
      rw [LeftExactHomology.homologyπ_leftExactHomologyComparison_assoc]
    _ = (LeftExactHomology.leftExactCyclesIso (S.map F) G).hom ≫
        G.map ((LeftExactHomology.leftExactCyclesIso S F).hom ≫ F.map S.homologyπ) := by
      rw [← G.map_comp, LeftExactHomology.homologyπ_leftExactHomologyComparison]
    _ = ((LeftExactHomology.leftExactCyclesIso (S.map F) G).hom ≫ G.map (LeftExactHomology.leftExactCyclesIso S F).hom) ≫
        G.map (F.map S.homologyπ) := by
      rw [G.map_comp, Category.assoc]
    _ = (LeftExactHomology.leftExactCyclesIso S (F ⋙ G)).hom ≫ (F ⋙ G).map S.homologyπ := by
      rw [leftExactCyclesIso_comp_hom]
      rfl
    _ = _ := (LeftExactHomology.homologyπ_leftExactHomologyComparison S (F ⋙ G)).symm

variable {G}

/-- For an exact functor, the canonical left-exact comparison agrees with
mathlib's ordinary homology-preservation isomorphism. -/
theorem leftExactHomologyComparison_eq_mapHomologyIso [PreservesFiniteColimits F] :
    LeftExactHomology.leftExactHomologyComparison S F = (S.mapHomologyIso F).hom := by
  rw [LeftExactHomologyIso.leftExactHomologyComparison_eq_mapHomologyIso',
    ShortComplex.mapHomologyIso'_eq_mapHomologyIso]

variable (G)

/-- If the second functor and the composite are exact, their actual
homology isomorphisms intertwine the first functor's left-exact comparison. -/
theorem mapHomologyIso_comp_leftExact [PreservesFiniteColimits G]
    [PreservesFiniteColimits (F ⋙ G)] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (LeftExactHomology.leftExactHomologyComparison S F) =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  rw [← leftExactHomologyComparison_eq_mapHomologyIso,
    leftExactHomologyComparison_comp, leftExactHomologyComparison_eq_mapHomologyIso]

end

end OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition
