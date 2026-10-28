import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology

/-! # Binary Small Complement Functoriality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.BinarySmallComplementFunctoriality

noncomputable section

/-!
# Functoriality of binary-small relative chain quotients

A continuous map carrying each of two subsets into its specified target
subset carries binary-small singular simplices to binary-small simplices.
The induced chain map descends through the actual cokernel, commutes with
the comparison to union-relative chains, and respects identities and
composition. No openness or quasi-isomorphism premise is used.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : TopCat.{0}} {A B : Set X} {A' B' : Set Y} {A'' B'' : Set Z}

/-- Whole-image containment of a singular simplex is preserved by an actual
continuous map of the specified subsets. -/
theorem subspaceSingularSubcomplex_le_preimage_of_mapsTo
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') :
    AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X A ≤
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex Y A').preimage (TopCat.toSSet.map f) := by
  intro n σ hσ
  change (TopCat.toSSet.map f).app n σ ∈ (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex Y A').obj n
  rw [AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex] at hσ ⊢
  rintro y ⟨t, rfl⟩
  change f (X.toSSetObjEquiv n σ t) ∈ A'
  exact hA (hσ ⟨t, rfl⟩)

/-- Binary-smallness is preserved by a continuous map of both subsets. -/
theorem binarySmallSubcomplex_le_preimage
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B ≤
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex Y A' B').preimage (TopCat.toSSet.map f) := by
  change AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X A ⊔ AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X B ≤
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex Y A' ⊔ AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.subspaceSingularSubcomplex Y B').preimage
      (TopCat.toSSet.map f)
  rw [SSet.Subcomplex.preimage_max]
  exact sup_le_sup (subspaceSingularSubcomplex_le_preimage_of_mapsTo f hA)
    (subspaceSingularSubcomplex_le_preimage_of_mapsTo f hB)

/-- The actual induced simplicial map on the binary-small subcomplexes. -/
def binarySmallSSetPairMap
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B : SSet) ⟶
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex Y A' B' : SSet) :=
  SSet.Subcomplex.homOfLE (binarySmallSubcomplex_le_preimage f hA hB) ≫
    (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex Y A' B').fromPreimage (TopCat.toSSet.map f)

@[reassoc (attr := simp)]
theorem binarySmallSSetPairMap_inclusion
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    binarySmallSSetPairMap f hA hB ≫ (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex Y A' B').ι =
      (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι ≫ TopCat.toSSet.map f := by
  rw [binarySmallSSetPairMap, Category.assoc, SSet.Subcomplex.fromPreimage_ι,
    ← Category.assoc, SSet.Subcomplex.homOfLE_ι]

/-- The actual chain map induced on binary-small integral singular chains. -/
def binarySmallChainPairMap
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ⟶ AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains Y A' B' :=
  AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (binarySmallSSetPairMap f hA hB)

@[reassoc (attr := simp)]
theorem binarySmallChainPairMap_inclusion
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    binarySmallChainPairMap f hA hB ≫ AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion Y A' B' =
      AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f := by
  rw [AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical,
    AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  change AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (binarySmallSSetPairMap f hA hB) ≫
      AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex Y A' B').ι =
    AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι ≫
      AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (TopCat.toSSet.map f)
  rw [← Functor.map_comp, binarySmallSSetPairMap_inclusion, Functor.map_comp]

/-- The actual cokernel map on quotients by binary-small chains. -/
def binarySmallComplementPairMap
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B ⟶ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains Y A' B' :=
  cokernel.map (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion Y A' B')
    (binarySmallChainPairMap f hA hB) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f)
    (binarySmallChainPairMap_inclusion f hA hB).symm

@[reassoc (attr := simp)]
theorem binarySmallComplementPairMap_projection
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B ≫ binarySmallComplementPairMap f hA hB =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection Y A' B' := by
  exact cokernel.π_desc _ _ _

/-- The induced quotient map commutes with the actual comparison to
relative chains of the union. -/
@[reassoc (attr := simp)]
theorem binarySmallComplementPairMap_toRelative
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    binarySmallComplementPairMap f hA hB ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative Y A' B' =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B ≫
        AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f (hA.union_union hB) := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).mp
  rw [← Category.assoc, binarySmallComplementPairMap_projection, Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_projection, ← Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative_projection, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality]

/-- The identity continuous map induces the identity on the quotient. -/
@[simp]
theorem binarySmallComplementPairMap_id (X : TopCat.{0}) (A B : Set X) :
    binarySmallComplementPairMap (𝟙 X) (A := A) (A' := A) (B := B) (B' := B)
      (fun _ hx => hx) (fun _ hx => hx) = 𝟙 _ := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).mp
  rw [binarySmallComplementPairMap_projection, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- The quotient maps compose in exactly the order of the continuous maps. -/
@[reassoc]
theorem binarySmallComplementPairMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B')
    (hA' : Set.MapsTo g A' A'') (hB' : Set.MapsTo g B' B'') :
    binarySmallComplementPairMap f hA hB ≫ binarySmallComplementPairMap g hA' hB' =
      binarySmallComplementPairMap (f ≫ g)
        (fun _ hx => hA' (hA hx)) (fun _ hx => hB' (hB hx)) := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).mp
  rw [← Category.assoc, binarySmallComplementPairMap_projection, Category.assoc,
    binarySmallComplementPairMap_projection, ← Category.assoc, ← Functor.map_comp,
    binarySmallComplementPairMap_projection]

@[reassoc (attr := simp)]
theorem binarySmallComplementPairMap_left
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B ≫ binarySmallComplementPairMap f hA hB =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f hA ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft Y A' B' := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)).mp
  rw [← Category.assoc, AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection,
    binarySmallComplementPairMap_projection, ← Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality, Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection]

@[reassoc (attr := simp)]
theorem binarySmallComplementPairMap_right
    (f : X ⟶ Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B ≫ binarySmallComplementPairMap f hA hB =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f hB ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight Y A' B' := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X B)).mp
  rw [← Category.assoc, AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_projection,
    binarySmallComplementPairMap_projection, ← Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality, Category.assoc,
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_projection]

end

end OAI.AlgebraicTopology.Duality.Poincare.BinarySmallComplementFunctoriality
