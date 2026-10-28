import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-! # Homology With Supports -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports

noncomputable section

/-!
# Relative singular homology with closed supports

The algebraic Mayer--Vietoris sequence starts with the actual quotients of
ordinary singular chains. The last quotient is by binary small chains;
subdivision identifies its homology with the relative homology of the union.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open ZeroObject

set_option backward.isDefEq.respectTransparency false

namespace Cycles

section Algebra

variable {C : Type*} [Category* C] [Abelian C]

/-- The direct sum of two cokernel projections is a cokernel of the direct
sum of the original maps. -/
def biprodCokernelIsColimit {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    IsColimit (CokernelCofork.ofπ
      (biprod.map (cokernel.π f) (cokernel.π g))
      (show biprod.map f g ≫ biprod.map (cokernel.π f) (cokernel.π g) = 0 by
        ext <;> simp)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun {T} k hk => by
    have hf : f ≫ biprod.inl ≫ k = 0 := by
      simpa using congrArg (fun t => biprod.inl ≫ t) hk
    have hg : g ≫ biprod.inr ≫ k = 0 := by
      simpa using congrArg (fun t => biprod.inr ≫ t) hk
    refine ⟨biprod.desc (cokernel.desc f (biprod.inl ≫ k) hf)
      (cokernel.desc g (biprod.inr ≫ k) hg), ?_⟩
    ext <;> simp)

/-- The split ambient sequence with signed diagonal and sum maps. -/
def signedAmbientSequence (W : C) : ShortComplex C :=
  (IsPushout.of_id_fst (f := 𝟙 W)).shortComplex

/-- The signed ambient sequence is short exact. -/
theorem signedAmbientSequence_shortExact (W : C) :
    (signedAmbientSequence W).ShortExact := by
  have hm : Mono (𝟙 W) := inferInstance
  have : Mono (signedAmbientSequence W).f := by
    exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hm (biprod.lift_fst _ _)
  have : Epi (signedAmbientSequence W).g :=
    (IsPushout.of_id_fst (f := 𝟙 W)).epi_shortComplex_g
  exact { exact := (IsPushout.of_id_fst (f := 𝟙 W)).exact_shortComplex }

end Algebra

variable (X : TopCat.{0})

/-- The relative chain map induced by increasing the subspace in a pair. -/
def relativeSubsetChainMap {A B : Set X} (h : A ⊆ B) :
    LocalHomology.Cycles.relativeSingularChains X A ⟶ LocalHomology.Cycles.relativeSingularChains X B :=
  LocalHomology.Cycles.relativeSingularChainsMap (𝟙 X) (fun _ hx => h hx)

@[reassoc (attr := simp)]
theorem relativeSubsetChainMap_projection {A B : Set X} (h : A ⊆ B) :
    LocalHomology.Cycles.relativeChainProjection X A ≫ relativeSubsetChainMap X h =
      LocalHomology.Cycles.relativeChainProjection X B := by
  rw [relativeSubsetChainMap, LocalHomology.Cycles.relativeChainProjection_naturality,
    CategoryTheory.Functor.map_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem subsetChainInclusion_comp {A B : Set X} (h : A ⊆ B) :
    LocalHomology.Cycles.integralSingularChainFunctor.map (SmallMayerVietoris.Cycles.subsetInclusion X h) ≫
      LocalHomology.Cycles.subspaceChainInclusion X B = LocalHomology.Cycles.subspaceChainInclusion X A := by
  change LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ LocalHomology.Cycles.integralSingularChainFunctor.map _ = _
  rw [← Functor.map_comp]
  rfl

variable (A B : Set X)

/-- The actual binary small-chain inclusion is a monomorphism. -/
instance binarySmallIntegralChainInclusion_mono :
    Mono (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) := by
  rw [BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical]
  infer_instance

/-- Ambient singular chains modulo chains subordinate to the binary family. -/
abbrev binarySmallComplementChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)

/-- Projection to the actual quotient by binary small chains. -/
abbrev binarySmallComplementProjection :
    LocalHomology.Cycles.integralSingularChains X ⟶ binarySmallComplementChains X A B :=
  cokernel.π (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)

@[reassoc (attr := simp)]
theorem subspaceChainInclusion_binarySmallComplement_left :
    LocalHomology.Cycles.subspaceChainInclusion X A ≫ binarySmallComplementProjection X A B = 0 := by
  unfold LocalHomology.Cycles.subspaceChainInclusion
  rw [← BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left X A B, Category.assoc]
  simp

@[reassoc (attr := simp)]
theorem subspaceChainInclusion_binarySmallComplement_right :
    LocalHomology.Cycles.subspaceChainInclusion X B ≫ binarySmallComplementProjection X A B = 0 := by
  unfold LocalHomology.Cycles.subspaceChainInclusion
  rw [← BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X A B, Category.assoc]
  simp

/-- The left relative quotient maps to the quotient by both small-chain pieces. -/
def binarySmallComplementLeft :
    LocalHomology.Cycles.relativeSingularChains X A ⟶ binarySmallComplementChains X A B :=
  cokernel.desc (LocalHomology.Cycles.subspaceChainInclusion X A) (binarySmallComplementProjection X A B)
    (subspaceChainInclusion_binarySmallComplement_left X A B)

/-- The right relative quotient maps to the quotient by both small-chain pieces. -/
def binarySmallComplementRight :
    LocalHomology.Cycles.relativeSingularChains X B ⟶ binarySmallComplementChains X A B :=
  cokernel.desc (LocalHomology.Cycles.subspaceChainInclusion X B) (binarySmallComplementProjection X A B)
    (subspaceChainInclusion_binarySmallComplement_right X A B)

@[reassoc (attr := simp)]
theorem binarySmallComplementLeft_projection :
    LocalHomology.Cycles.relativeChainProjection X A ≫ binarySmallComplementLeft X A B =
      binarySmallComplementProjection X A B := cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
theorem binarySmallComplementRight_projection :
    LocalHomology.Cycles.relativeChainProjection X B ≫ binarySmallComplementRight X A B =
      binarySmallComplementProjection X A B := cokernel.π_desc _ _ _

/-- The quotient sequence with intersection-relative left term and the actual
quotient by binary small chains as right term. -/
def binaryRelativeChainSequence :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) where
  X₁ := LocalHomology.Cycles.relativeSingularChains X (A ∩ B)
  X₂ := LocalHomology.Cycles.relativeSingularChains X A ⊞ LocalHomology.Cycles.relativeSingularChains X B
  X₃ := binarySmallComplementChains X A B
  f := biprod.lift (relativeSubsetChainMap X Set.inter_subset_left)
    (-relativeSubsetChainMap X Set.inter_subset_right)
  g := biprod.desc (binarySmallComplementLeft X A B) (binarySmallComplementRight X A B)
  zero := by
    apply (cancel_epi (LocalHomology.Cycles.relativeChainProjection X (A ∩ B))).mp
    simp

/-- The small-chain sequence maps into the split ambient sequence by its
actual inclusions. -/
def smallToAmbientSequenceMap :
    SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B ⟶ signedAmbientSequence (LocalHomology.Cycles.integralSingularChains X) where
  τ₁ := LocalHomology.Cycles.subspaceChainInclusion X (A ∩ B)
  τ₂ := biprod.map (LocalHomology.Cycles.subspaceChainInclusion X A) (LocalHomology.Cycles.subspaceChainInclusion X B)
  τ₃ := BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B
  comm₁₂ := by
    apply biprod.hom_ext <;> simp [signedAmbientSequence] <;> exact Category.comp_id _
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp [signedAmbientSequence, BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left]
    · simp [signedAmbientSequence, BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right]

/-- Projection from the split ambient sequence to its three actual quotients. -/
def ambientToRelativeSequenceMap :
    signedAmbientSequence (LocalHomology.Cycles.integralSingularChains X) ⟶ binaryRelativeChainSequence X A B where
  τ₁ := LocalHomology.Cycles.relativeChainProjection X (A ∩ B)
  τ₂ := biprod.map (LocalHomology.Cycles.relativeChainProjection X A) (LocalHomology.Cycles.relativeChainProjection X B)
  τ₃ := binarySmallComplementProjection X A B
  comm₁₂ := by
    apply biprod.hom_ext <;> simp [signedAmbientSequence, binaryRelativeChainSequence] <;>
      exact (Category.id_comp _).symm
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp [signedAmbientSequence, binaryRelativeChainSequence]

/-- The exact quotient sequence is obtained by the actual snake diagram. -/
def binaryRelativeSnakeInput :
    ShortComplex.SnakeInput (ChainComplex (ModuleCat.{0} ℤ) ℕ) where
  L₀ := ShortComplex.mk (0 : (0 : ChainComplex (ModuleCat.{0} ℤ) ℕ) ⟶ 0)
    (0 : (0 : ChainComplex (ModuleCat.{0} ℤ) ℕ) ⟶ 0) (by simp)
  L₁ := SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B
  L₂ := signedAmbientSequence (LocalHomology.Cycles.integralSingularChains X)
  L₃ := binaryRelativeChainSequence X A B
  v₀₁ := 0
  v₁₂ := smallToAmbientSequenceMap X A B
  v₂₃ := ambientToRelativeSequenceMap X A B
  w₁₃ := by
    apply ShortComplex.hom_ext
    · exact cokernel.condition _
    · change biprod.map _ _ ≫ biprod.map _ _ = 0
      apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
    · exact cokernel.condition _
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2
    · exact kernel.isLimitConeZeroCone (LocalHomology.Cycles.subspaceChainInclusion X (A ∩ B))
    · exact kernel.isLimitConeZeroCone
        (biprod.map (LocalHomology.Cycles.subspaceChainInclusion X A) (LocalHomology.Cycles.subspaceChainInclusion X B))
    · exact kernel.isLimitConeZeroCone (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
    · exact cokernelIsCokernel _
    · exact biprodCokernelIsColimit _ _
    · exact cokernelIsCokernel _
  L₁_exact := (SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X A B).exact
  epi_L₁_g := (SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X A B).epi_g
  L₂_exact := (signedAmbientSequence_shortExact (LocalHomology.Cycles.integralSingularChains X)).exact
  mono_L₂_f := (signedAmbientSequence_shortExact (LocalHomology.Cycles.integralSingularChains X)).mono_f

/-- The quotient-chain Mayer--Vietoris sequence is short exact for arbitrary
subsets. No openness or excision is required at this algebraic stage. -/
theorem binaryRelativeChainSequence_shortExact :
    (binaryRelativeChainSequence X A B).ShortExact := by
  let S := binaryRelativeSnakeInput X A B
  have : Epi S.L₂.g := (signedAmbientSequence_shortExact (LocalHomology.Cycles.integralSingularChains X)).epi_g
  exact {
    exact := S.L₃_exact
    mono_f := S.L₂'_exact.mono_g (isZero_zero _ |>.eq_of_src _ _)
    epi_g := S.epi_L₃_g }

/-- The quotient sequence for inclusion of the binary small chains in the
ambient singular chains. -/
def binarySmallComplementSequence :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)
    (binarySmallComplementProjection X A B) (cokernel.condition _)

theorem binarySmallComplementSequence_shortExact :
    (binarySmallComplementSequence X A B).ShortExact := by
  change (ShortComplex.mk (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)
    (cokernel.π _) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact _ }

/-- The canonical comparison from the small-chain quotient to the actual
relative singular chains for the union. -/
def binarySmallComplementToRelative :
    binarySmallComplementChains X A B ⟶ LocalHomology.Cycles.relativeSingularChains X (A ∪ B) :=
  cokernel.map (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)
    (LocalHomology.Cycles.subspaceChainInclusion X (A ∪ B)) (BinarySmallUnion.Cycles.binarySmallToUnionChainMap X A B) (𝟙 _)
    (by simpa using (BinarySmallUnion.Cycles.binarySmallToUnionChainMap_inclusion X A B).symm)

@[reassoc (attr := simp)]
theorem binarySmallComplementToRelative_projection :
    binarySmallComplementProjection X A B ≫ binarySmallComplementToRelative X A B =
      LocalHomology.Cycles.relativeChainProjection X (A ∪ B) := by
  simp [binarySmallComplementToRelative]

/-- The comparison of the two actual quotient short exact sequences. -/
def binarySmallComplementSequenceMap :
    binarySmallComplementSequence X A B ⟶ LocalHomology.Cycles.relativeChainSequence X (A ∪ B) where
  τ₁ := BinarySmallUnion.Cycles.binarySmallToUnionChainMap X A B
  τ₂ := 𝟙 _
  τ₃ := binarySmallComplementToRelative X A B
  comm₁₂ := by
    change BinarySmallUnion.Cycles.binarySmallToUnionChainMap X A B ≫ LocalHomology.Cycles.subspaceChainInclusion X (A ∪ B) =
      BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B ≫ 𝟙 _
    rw [Category.comp_id]
    exact BinarySmallUnion.Cycles.binarySmallToUnionChainMap_inclusion X A B
  comm₂₃ := by
    change 𝟙 _ ≫ LocalHomology.Cycles.relativeChainProjection X (A ∪ B) =
      binarySmallComplementProjection X A B ≫ binarySmallComplementToRelative X A B
    rw [Category.id_comp]
    exact (binarySmallComplementToRelative_projection X A B).symm

/-- Subdivision and the quotient homology sequences prove that the last
quotient computes the actual relative homology of the union. -/
theorem binarySmallComplementToRelative_quasiIso (hA : IsOpen A) (hB : IsOpen B) :
    _root_.QuasiIso (binarySmallComplementToRelative X A B) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (binarySmallComplementSequenceMap X A B)
    (binarySmallComplementSequence_shortExact X A B)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X (A ∪ B))
    (BinarySmallUnion.Cycles.binarySmallToUnionChainMap_quasiIso X A B hA hB)
    (by change _root_.QuasiIso (𝟙 _); infer_instance)

/-- The comparison isomorphism induced by the actual quotient map. -/
def binarySmallComplementHomologyIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binarySmallComplementChains X A B).homology n ≅
      LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) n := by
  have := binarySmallComplementToRelative_quasiIso X A B hA hB
  exact isoOfQuasiIsoAt (binarySmallComplementToRelative X A B) n

@[simp]
theorem binarySmallComplementHomologyIso_hom (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (binarySmallComplementHomologyIso X A B hA hB n).hom =
      HomologicalComplex.homologyMap (binarySmallComplementToRelative X A B) n := rfl

@[reassoc (attr := simp)]
theorem binarySmallComplementLeft_toRelative :
    binarySmallComplementLeft X A B ≫ binarySmallComplementToRelative X A B =
      relativeSubsetChainMap X (Set.subset_union_left : A ⊆ A ∪ B) := by
  apply (cancel_epi (LocalHomology.Cycles.relativeChainProjection X A)).mp
  simp

@[reassoc (attr := simp)]
theorem binarySmallComplementRight_toRelative :
    binarySmallComplementRight X A B ≫ binarySmallComplementToRelative X A B =
      relativeSubsetChainMap X (Set.subset_union_right : B ⊆ A ∪ B) := by
  apply (cancel_epi (LocalHomology.Cycles.relativeChainProjection X B)).mp
  simp

/-- Homology of the middle chain biproduct is the biproduct of the two
actual relative homology groups. -/
def binaryRelativeMiddleHomologyIso (n : ℕ) :
    (binaryRelativeChainSequence X A B).X₂.homology n ≅
      LocalHomology.Cycles.relativeSingularHomology X A n ⊞ LocalHomology.Cycles.relativeSingularHomology X B n := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n
  letI : PreservesBinaryBiproduct
      (LocalHomology.Cycles.relativeSingularChains X A) (LocalHomology.Cycles.relativeSingularChains X B) F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  exact F.mapBiprod _ _

@[simp]
theorem binaryRelativeMiddleHomologyIso_hom (n : ℕ) :
    (binaryRelativeMiddleHomologyIso X A B n).hom =
      biprod.lift (HomologicalComplex.homologyMap biprod.fst n)
        (HomologicalComplex.homologyMap biprod.snd n) := rfl

@[simp]
theorem binaryRelativeMiddleHomologyIso_inv (n : ℕ) :
    (binaryRelativeMiddleHomologyIso X A B n).inv =
      biprod.desc (HomologicalComplex.homologyMap biprod.inl n)
        (HomologicalComplex.homologyMap biprod.inr n) := rfl

/-- The first relative Mayer--Vietoris map, with its canonical signs. -/
def relativeMayerVietorisFirst (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X (A ∩ B) n ⟶
      LocalHomology.Cycles.relativeSingularHomology X A n ⊞ LocalHomology.Cycles.relativeSingularHomology X B n :=
  HomologicalComplex.homologyMap (binaryRelativeChainSequence X A B).f n ≫
    (binaryRelativeMiddleHomologyIso X A B n).hom

/-- The second relative Mayer--Vietoris map induced by the two quotient maps. -/
def relativeMayerVietorisSecond (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X A n ⊞ LocalHomology.Cycles.relativeSingularHomology X B n ⟶
      LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) n :=
  (binaryRelativeMiddleHomologyIso X A B n).inv ≫
    HomologicalComplex.homologyMap (binaryRelativeChainSequence X A B).g n ≫
      HomologicalComplex.homologyMap (binarySmallComplementToRelative X A B) n

/-- The connecting map for the actual pairs, using the proved small-chain
comparison for open subsets. -/
def relativeMayerVietorisBoundary (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (n + 1) ⟶
      LocalHomology.Cycles.relativeSingularHomology X (A ∩ B) n :=
  (binarySmallComplementHomologyIso X A B hA hB (n + 1)).inv ≫
    (binaryRelativeChainSequence_shortExact X A B).δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem relativeMayerVietorisFirst_fst (n : ℕ) :
    relativeMayerVietorisFirst X A B n ≫ biprod.fst =
      HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.inter_subset_left : A ∩ B ⊆ A)) n := by
  simp only [relativeMayerVietorisFirst, Category.assoc,
    binaryRelativeMiddleHomologyIso_hom, biprod.lift_fst]
  rw [← HomologicalComplex.homologyMap_comp]
  simp [binaryRelativeChainSequence]

@[reassoc (attr := simp)]
theorem relativeMayerVietorisFirst_snd (n : ℕ) :
    relativeMayerVietorisFirst X A B n ≫ biprod.snd =
      -HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.inter_subset_right : A ∩ B ⊆ B)) n := by
  simp only [relativeMayerVietorisFirst, Category.assoc,
    binaryRelativeMiddleHomologyIso_hom, biprod.lift_snd]
  rw [← HomologicalComplex.homologyMap_comp]
  simp [binaryRelativeChainSequence]

@[reassoc (attr := simp)]
theorem relativeMayerVietorisSecond_inl (n : ℕ) :
    biprod.inl ≫ relativeMayerVietorisSecond X A B n =
      HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.subset_union_left : A ⊆ A ∪ B)) n := by
  simp only [relativeMayerVietorisSecond, binaryRelativeMiddleHomologyIso_inv,
    biprod.inl_desc_assoc]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  simp [binaryRelativeChainSequence]

@[reassoc (attr := simp)]
theorem relativeMayerVietorisSecond_inr (n : ℕ) :
    biprod.inr ≫ relativeMayerVietorisSecond X A B n =
      HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.subset_union_right : B ⊆ A ∪ B)) n := by
  simp only [relativeMayerVietorisSecond, binaryRelativeMiddleHomologyIso_inv,
    biprod.inr_desc_assoc]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  simp [binaryRelativeChainSequence]

/-- Six consecutive terms in Mayer--Vietoris for the genuine relative pairs. -/
def relativeMayerVietorisHomologySequence (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℤ) 5 :=
  ComposableArrows.mk₅ (relativeMayerVietorisFirst X A B (n + 1))
    (relativeMayerVietorisSecond X A B (n + 1))
    (relativeMayerVietorisBoundary X A B hA hB n)
    (relativeMayerVietorisFirst X A B n) (relativeMayerVietorisSecond X A B n)

/-- Every term and arrow agrees with the genuine quotient homology sequence
through the canonical biproduct and small-chain comparison isomorphisms. -/
def relativeMayerVietorisHomologySequenceIso (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    HomologicalComplex.HomologySequence.composableArrows₅
      (binaryRelativeChainSequence_shortExact X A B) (n + 1) n rfl ≅
        relativeMayerVietorisHomologySequence X A B hA hB n := by
  refine ComposableArrows.isoMk₅ (Iso.refl _) (binaryRelativeMiddleHomologyIso X A B (n + 1))
    (binarySmallComplementHomologyIso X A B hA hB (n + 1))
    (Iso.refl _) (binaryRelativeMiddleHomologyIso X A B n)
    (binarySmallComplementHomologyIso X A B hA hB n) ?_ ?_ ?_ ?_ ?_
  · change HomologicalComplex.homologyMap (binaryRelativeChainSequence X A B).f (n + 1) ≫
      (binaryRelativeMiddleHomologyIso X A B (n + 1)).hom = 𝟙 _ ≫ _
    exact (Category.id_comp _).symm
  · change _ = (binaryRelativeMiddleHomologyIso X A B (n + 1)).hom ≫
      (binaryRelativeMiddleHomologyIso X A B (n + 1)).inv ≫ _
    rw [Iso.hom_inv_id_assoc]
    rfl
  · change (binaryRelativeChainSequence_shortExact X A B).δ (n + 1) n rfl ≫ 𝟙 _ =
      (binarySmallComplementHomologyIso X A B hA hB (n + 1)).hom ≫
      (binarySmallComplementHomologyIso X A B hA hB (n + 1)).inv ≫
      (binaryRelativeChainSequence_shortExact X A B).δ (n + 1) n rfl
    rw [Iso.hom_inv_id_assoc, Category.comp_id]
  · change HomologicalComplex.homologyMap (binaryRelativeChainSequence X A B).f n ≫
      (binaryRelativeMiddleHomologyIso X A B n).hom = 𝟙 _ ≫ _
    exact (Category.id_comp _).symm
  · change _ = (binaryRelativeMiddleHomologyIso X A B n).hom ≫
      (binaryRelativeMiddleHomologyIso X A B n).inv ≫ _
    rw [Iso.hom_inv_id_assoc]
    rfl

/-- Mayer--Vietoris exactness for actual relative singular homology; no
Mayer--Vietoris or excision assumption is used. -/
theorem relativeMayerVietorisHomologySequence_exact
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (relativeMayerVietorisHomologySequence X A B hA hB n).Exact :=
  ComposableArrows.exact_of_iso (relativeMayerVietorisHomologySequenceIso X A B hA hB n)
    (HomologicalComplex.HomologySequence.composableArrows₅_exact
      (binaryRelativeChainSequence_shortExact X A B) (n + 1) n rfl)

/-- Exactness at the direct sum, expressed in the underlying modules. -/
theorem relativeMayerVietoris_range_first (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeMayerVietorisFirst X A B n).hom =
      LinearMap.ker (relativeMayerVietorisSecond X A B n).hom :=
  ((relativeMayerVietorisHomologySequence_exact X A B hA hB n).exact 3).moduleCat_range_eq_ker

/-- Exactness at the union-relative term. -/
theorem relativeMayerVietoris_range_second (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeMayerVietorisSecond X A B (n + 1)).hom =
      LinearMap.ker (relativeMayerVietorisBoundary X A B hA hB n).hom :=
  ((relativeMayerVietorisHomologySequence_exact X A B hA hB n).exact 1).moduleCat_range_eq_ker

/-- Exactness at the intersection-relative term. -/
theorem relativeMayerVietoris_range_boundary (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeMayerVietorisBoundary X A B hA hB n).hom =
      LinearMap.ker (relativeMayerVietorisFirst X A B n).hom :=
  ((relativeMayerVietorisHomologySequence_exact X A B hA hB n).exact 2).moduleCat_range_eq_ker

/-- Compatible classes in the two relative groups glue to a class for the
intersection-relative pair. This is the usual closed-support gluing statement
after taking the two open complements. -/
theorem relativeMayerVietoris_glue (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (a : LocalHomology.Cycles.relativeSingularHomology X A n) (b : LocalHomology.Cycles.relativeSingularHomology X B n)
    (hab : (HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.subset_union_left : A ⊆ A ∪ B)) n).hom a =
      (HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.subset_union_right : B ⊆ A ∪ B)) n).hom b) :
    ∃ c : LocalHomology.Cycles.relativeSingularHomology X (A ∩ B) n,
      (HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.inter_subset_left : A ∩ B ⊆ A)) n).hom c = a ∧
      (HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.inter_subset_right : A ∩ B ⊆ B)) n).hom c = b := by
  let z : (LocalHomology.Cycles.relativeSingularHomology X A n ⊞ LocalHomology.Cycles.relativeSingularHomology X B n : ModuleCat ℤ) :=
    (biprod.inl : LocalHomology.Cycles.relativeSingularHomology X A n ⟶ _).hom a -
      (biprod.inr : LocalHomology.Cycles.relativeSingularHomology X B n ⟶ _).hom b
  have hz : z ∈ LinearMap.ker (relativeMayerVietorisSecond X A B n).hom := by
    change (relativeMayerVietorisSecond X A B n).hom z = 0
    have ha := congrArg (fun t : LocalHomology.Cycles.relativeSingularHomology X A n ⟶
        LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) n => t.hom a)
      (relativeMayerVietorisSecond_inl X A B n)
    have hb := congrArg (fun t : LocalHomology.Cycles.relativeSingularHomology X B n ⟶
        LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) n => t.hom b)
      (relativeMayerVietorisSecond_inr X A B n)
    dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ha hb
    simp only [z, map_sub, ha, hb, hab, sub_self]
  rw [← relativeMayerVietoris_range_first X A B hA hB n] at hz
  obtain ⟨c, hc⟩ := hz
  refine ⟨c, ?_, ?_⟩
  · have he := congrArg
      (fun t => (biprod.fst : LocalHomology.Cycles.relativeSingularHomology X A n ⊞
        LocalHomology.Cycles.relativeSingularHomology X B n ⟶ LocalHomology.Cycles.relativeSingularHomology X A n).hom t) hc
    change (relativeMayerVietorisFirst X A B n ≫ biprod.fst).hom c = _ at he
    rw [relativeMayerVietorisFirst_fst] at he
    simpa [z, ← ModuleCat.comp_apply] using he
  · have he := congrArg
      (fun t => (biprod.snd : LocalHomology.Cycles.relativeSingularHomology X A n ⊞
        LocalHomology.Cycles.relativeSingularHomology X B n ⟶ LocalHomology.Cycles.relativeSingularHomology X B n).hom t) hc
    change (relativeMayerVietorisFirst X A B n ≫ biprod.snd).hom c = _ at he
    rw [relativeMayerVietorisFirst_snd] at he
    have hn : -(HomologicalComplex.homologyMap
        (relativeSubsetChainMap X (Set.inter_subset_right : A ∩ B ⊆ B)) n).hom c = -b := by
      simpa [z, ← ModuleCat.comp_apply] using he
    exact neg_injective hn

/-- Ordinary singular homology with support in a subset means the actual
relative homology of the complement pair. -/
abbrev singularHomologyWithSupport (K : Set X) (n : ℕ) : ModuleCat.{0} ℤ :=
  LocalHomology.Cycles.relativeSingularHomology X Kᶜ n

/-- Mayer--Vietoris with closed supports, obtained by the two open complements. -/
def homologyWithSupportMayerVietorisSequence (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℤ) 5 :=
  relativeMayerVietorisHomologySequence X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n

/-- The supports sequence is exact for closed subsets. -/
theorem homologyWithSupportMayerVietorisSequence_exact (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (homologyWithSupportMayerVietorisSequence X K L hK hL n).Exact :=
  relativeMayerVietorisHomologySequence_exact X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n

/-- The first term is homology with support in the union. -/
theorem homologyWithSupportMayerVietorisSequence_obj_zero (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (homologyWithSupportMayerVietorisSequence X K L hK hL n).obj' 0 =
      singularHomologyWithSupport X (K ∪ L) (n + 1) := by
  change LocalHomology.Cycles.relativeSingularHomology X (Kᶜ ∩ Lᶜ) (n + 1) =
    LocalHomology.Cycles.relativeSingularHomology X (K ∪ L)ᶜ (n + 1)
  rw [Set.compl_union]

/-- The middle term is the direct sum of the individual support groups. -/
theorem homologyWithSupportMayerVietorisSequence_obj_one (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (homologyWithSupportMayerVietorisSequence X K L hK hL n).obj' 1 =
      (singularHomologyWithSupport X K (n + 1) ⊞
        singularHomologyWithSupport X L (n + 1)) := rfl

/-- The third term is homology with support in the intersection. -/
theorem homologyWithSupportMayerVietorisSequence_obj_two (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (homologyWithSupportMayerVietorisSequence X K L hK hL n).obj' 2 =
      singularHomologyWithSupport X (K ∩ L) (n + 1) := by
  change LocalHomology.Cycles.relativeSingularHomology X (Kᶜ ∪ Lᶜ) (n + 1) =
    LocalHomology.Cycles.relativeSingularHomology X (K ∩ L)ᶜ (n + 1)
  rw [Set.compl_inter]

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
