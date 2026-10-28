import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso

/-! # Binary Small Union -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion.Cycles

noncomputable section

/-!
# Binary small chains and the singular chains of the union

The small singular simplices for two subsets of an ambient space can be
viewed in their union without changing the simplicial set. If the subsets
are open, the previously proved open-cover comparison on that union shows
that the canonical map from these small chains to all chains of the union
is a quasi-isomorphism.
-/

open _root_.CategoryTheory

/-- Containment of a singular simplex in a subspace is preserved when
the ambient space itself is restricted to another subspace. -/
theorem subspaceSingularSubcomplex_preimage (X : TopCat.{0}) (C A : Set X) :
    SmallMayerVietoris.Cycles.subspaceSingularSubcomplex (TopCat.of C) (Subtype.val ⁻¹' A) =
      (SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X A).preimage
        (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X C)) := by
  ext n σ
  change σ ∈ (SmallMayerVietoris.Cycles.subspaceSingularSubcomplex (TopCat.of C) (Subtype.val ⁻¹' A)).obj n ↔
    (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X C)).app n σ ∈
      (SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X A).obj n
  rw [SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex, SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex]
  constructor
  · intro h x hx
    obtain ⟨t, rfl⟩ := hx
    exact h ⟨t, rfl⟩
  · intro h x hx
    obtain ⟨t, rfl⟩ := hx
    exact h ⟨t, rfl⟩

/-- Inclusion of subsets gives inclusion of their contained-simplex
subcomplexes. -/
theorem subspaceSingularSubcomplex_mono (X : TopCat.{0}) {A B : Set X}
    (h : A ⊆ B) : SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X A ≤ SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X B := by
  intro n σ hσ
  rw [SmallMayerVietoris.Cycles.mem_subspaceSingularSubcomplex] at hσ ⊢
  exact hσ.trans h

/-- The binary small-simplex condition commutes with restriction of the
ambient space to a subspace. -/
theorem binarySmallSingularSubcomplex_preimage (X : TopCat.{0}) (C A B : Set X) :
    SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex (TopCat.of C)
        (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) =
      (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).preimage
        (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X C)) := by
  dsimp only [SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex]
  rw [SSet.Subcomplex.preimage_max, subspaceSingularSubcomplex_preimage,
    subspaceSingularSubcomplex_preimage]

/-- Every binary small simplex is contained in the union. -/
theorem binarySmallSingularSubcomplex_le_union (X : TopCat.{0}) (A B : Set X) :
    SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B ≤ SmallMayerVietoris.Cycles.subspaceSingularSubcomplex X (A ∪ B) :=
  sup_le (subspaceSingularSubcomplex_mono X Set.subset_union_left)
    (subspaceSingularSubcomplex_mono X Set.subset_union_right)

/-- Restricting an injective simplicial map to the preimage of a
subcomplex in its range yields an isomorphism onto that subcomplex. -/
theorem subcomplexFromPreimage_isIso {S T : SSet.{0}} (f : S ⟶ T) [Mono f]
    (P : T.Subcomplex) (hP : P ≤ SSet.Subcomplex.range f) :
    IsIso (P.fromPreimage f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    apply Subtype.ext
    apply (mono_iff_injective (f.app n)).mp inferInstance
    exact congrArg Subtype.val h
  · intro y
    obtain ⟨x, hx⟩ := hP n y.property
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change f.app n x ∈ P.obj n
      rw [hx]
      exact y.property
    · exact Subtype.ext hx

variable (X : TopCat.{0}) (A B : Set X)

/-- The first subset regarded as a subset of the actual union space. -/
abbrev binaryUnionFirst : Set (TopCat.of (A ∪ B : Set X)) := Subtype.val ⁻¹' A

/-- The second subset regarded as a subset of the actual union space. -/
abbrev binaryUnionSecond : Set (TopCat.of (A ∪ B : Set X)) := Subtype.val ⁻¹' B

/-- The two restricted subsets cover the union space. -/
theorem binaryUnion_cover : binaryUnionFirst X A B ∪ binaryUnionSecond X A B = Set.univ := by
  ext x
  change (x.val ∈ A ∨ x.val ∈ B) ↔ True
  exact iff_true_intro x.property

theorem binaryUnionFirst_isOpen (hA : IsOpen A) : IsOpen (binaryUnionFirst X A B) :=
  hA.preimage continuous_subtype_val

theorem binaryUnionSecond_isOpen (hB : IsOpen B) : IsOpen (binaryUnionSecond X A B) :=
  hB.preimage continuous_subtype_val

/-- Forgetting the union subspace changes no binary small simplex.
The isomorphism maps each simplex by the actual subspace inclusion. -/
def binarySmallUnionSSetIso :
    (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex (TopCat.of (A ∪ B : Set X))
      (binaryUnionFirst X A B) (binaryUnionSecond X A B) : SSet) ≅
    (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B : SSet) :=
  SSet.Subcomplex.eqToIso (binarySmallSingularSubcomplex_preimage X (A ∪ B) A B) ≪≫
    @asIso _ _ _ _
      ((SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).fromPreimage
        (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X (A ∪ B))))
      (subcomplexFromPreimage_isIso _ _ (binarySmallSingularSubcomplex_le_union X A B))

/-- The small-simplex isomorphism has the expected ambient inclusion. -/
@[reassoc]
theorem binarySmallUnionSSetIso_hom_inclusion :
    (binarySmallUnionSSetIso X A B).hom ≫ (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι =
      (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex (TopCat.of (A ∪ B : Set X))
        (binaryUnionFirst X A B) (binaryUnionSecond X A B)).ι ≫
        TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X (A ∪ B)) := by
  change ((SSet.Subcomplex.eqToIso
      (binarySmallSingularSubcomplex_preimage X (A ∪ B) A B)).hom ≫
      (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).fromPreimage
        (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X (A ∪ B)))) ≫
      (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι = _
  rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι, ← Category.assoc]
  rfl

/-- The canonical corestriction of a binary small simplex to the union. -/
def binarySmallToUnionSSetMap :
    (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B : SSet) ⟶
      TopCat.toSSet.obj (TopCat.of (A ∪ B : Set X)) :=
  (binarySmallUnionSSetIso X A B).inv ≫
    (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex (TopCat.of (A ∪ B : Set X))
      (binaryUnionFirst X A B) (binaryUnionSecond X A B)).ι

/-- Corestriction followed by subspace inclusion is the original simplex. -/
@[reassoc]
theorem binarySmallToUnionSSetMap_inclusion :
    binarySmallToUnionSSetMap X A B ≫ TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X (A ∪ B)) =
      (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι := by
  dsimp only [binarySmallToUnionSSetMap]
  rw [Category.assoc, ← binarySmallUnionSSetIso_hom_inclusion]
  simp

/-- The actual integral chain map corestricting binary small simplices
to their union. -/
def binarySmallToUnionChainMap :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ⟶ LocalHomology.Cycles.integralSingularChains (TopCat.of (A ∪ B : Set X)) :=
  SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (binarySmallToUnionSSetMap X A B)

/-- The triangle used to compare cokernels with relative chains. -/
@[reassoc]
theorem binarySmallToUnionChainMap_inclusion :
    binarySmallToUnionChainMap X A B ≫ LocalHomology.Cycles.subspaceChainInclusion X (A ∪ B) =
      BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B := by
  rw [BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  change SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (binarySmallToUnionSSetMap X A B) ≫
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map
        (TopCat.toSSet.map (LocalHomology.Cycles.subspaceInclusion X (A ∪ B))) = _
  rw [← Functor.map_comp, binarySmallToUnionSSetMap_inclusion]

/-- Binary small chains compute the actual homology of the union for
open subsets, even when their union is smaller than the ambient space. -/
theorem binarySmallToUnionChainMap_quasiIso (hA : IsOpen A) (hB : IsOpen B) :
    _root_.QuasiIso (binarySmallToUnionChainMap X A B) := by
  have hsmall := SmallSingularQuasiIso.Cycles.binarySmallIntegralChainInclusion_quasiIso (TopCat.of (A ∪ B : Set X))
    (binaryUnionFirst X A B) (binaryUnionSecond X A B)
    (binaryUnionFirst_isOpen X A B hA) (binaryUnionSecond_isOpen X A B hB)
    (binaryUnion_cover X A B)
  dsimp only [binarySmallToUnionChainMap, binarySmallToUnionSSetMap]
  rw [Functor.map_comp, ← BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  exact quasiIso_comp _ _ (hφ' := hsmall)

/-- The isomorphism on ordinary homology is induced by the displayed
canonical chain map. -/
def binarySmallUnionHomologyIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X A B n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (A ∪ B : Set X)) n := by
  letI := binarySmallToUnionChainMap_quasiIso X A B hA hB
  exact isoOfQuasiIsoAt (binarySmallToUnionChainMap X A B) n

@[simp]
theorem binarySmallUnionHomologyIso_hom (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binarySmallUnionHomologyIso X A B hA hB n).hom =
      HomologicalComplex.homologyMap (binarySmallToUnionChainMap X A B) n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion.Cycles
