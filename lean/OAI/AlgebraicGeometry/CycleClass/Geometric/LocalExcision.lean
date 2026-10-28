import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Local Excision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision

noncomputable section

/-!
# Local excision for actual integral singular homology

The relative-cover comparison starts from the actual binary small-chain
pushout. Its quotient identifies relative chains in one cover member with
small chains modulo the other cover member.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable (X : TopCat.{0}) (U A : Set X)

/-- The subspace of `U` lying in `A` is the actual intersection subspace of `X`. -/
def relativeIntersectionHomeomorph :
    ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ≃ₜ (U ∩ A : Set X) where
  toFun u := ⟨u.1.1, u.1.2, u.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The map from the intersection, viewed inside `U`, to the second subspace. -/
def relativeIntersectionToRight :
    TopCat.of ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ⟶ TopCat.of A :=
  LocalHomology.Cycles.subspaceMap (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- The binary small-chain pushout expressed using the genuine relative-pair
subspace in `U`. -/
theorem relativeCover_isPushout :
    IsPushout
      (LocalHomology.Cycles.subspaceChainInclusion (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A))
      (LocalHomology.Cycles.integralSingularChainFunctor.map (relativeIntersectionToRight X U A))
      (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A))
      (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)) := by
  refine (SmallMayerVietoris.Cycles.binarySmallChain_isPushout X U A).of_iso'
    (LocalHomology.Cycles.integralSingularChainFunctor.mapIso
      (TopCat.isoOfHomeo (relativeIntersectionHomeomorph X U A)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ LocalHomology.Cycles.integralSingularChainFunctor.map _ =
      LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    rfl
  · change LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ LocalHomology.Cycles.integralSingularChainFunctor.map _ =
      LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    rfl
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The actual binary-cover small chains modulo chains in the second member. -/
abbrev binarySmallRelativeChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))

/-- Projection from binary small chains to their quotient by chains in `A`. -/
abbrev binarySmallRelativeProjection :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X U A ⟶ binarySmallRelativeChains X U A :=
  cokernel.π (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))

/-- The canonical relative-cover quotient map, induced by inclusion of `U`. -/
def relativeCoverCokernelMap :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ⟶
      binarySmallRelativeChains X U A :=
  cokernel.map
    (LocalHomology.Cycles.subspaceChainInclusion (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A))
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (LocalHomology.Cycles.integralSingularChainFunctor.map (relativeIntersectionToRight X U A))
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A))
    (relativeCover_isPushout X U A).w

/-- A pushout preserves the quotient by the opposite cover member. -/
instance relativeCoverCokernelMap_isIso : IsIso (relativeCoverCokernelMap X U A) :=
  isIso_cokernel_map_of_isPushout (relativeCover_isPushout X U A)

/-- Relative chains in `U` are exactly small chains modulo chains in `A`. -/
def relativeCoverCokernelIso :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ≅
      binarySmallRelativeChains X U A :=
  asIso (relativeCoverCokernelMap X U A)

/-- The quotient identification is induced by the actual inclusion of `U`. -/
@[reassoc (attr := simp)]
theorem relativeCoverCokernelMap_projection :
    LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ≫
        relativeCoverCokernelMap X U A =
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A) ≫
        binarySmallRelativeProjection X U A :=
  cokernel.π_desc _ _ _

/-- The actual map of relative chain complexes induced by inclusion of `U`. -/
def relativeCoverInclusion :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ⟶
      LocalHomology.Cycles.relativeSingularChains X A :=
  LocalHomology.Cycles.relativeSingularChainsMap (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- Chains in the second member inject into the actual binary small chains. -/
instance binarySmallSingularRight_chain_mono :
    Mono (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)) :=
  mono_of_mono_fac (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A)

/-- The quotient sequence for actual small chains relative to `A`. -/
def binarySmallRelativeSequence :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (binarySmallRelativeProjection X U A) (cokernel.condition _)

/-- The quotient sequence of small relative chains is short exact. -/
theorem binarySmallRelativeSequence_shortExact :
    (binarySmallRelativeSequence X U A).ShortExact := by
  change (ShortComplex.mk
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (cokernel.π _) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact _ }

/-- Canonical inclusion from small relative chains to all relative chains. -/
def binarySmallRelativeInclusion :
    binarySmallRelativeChains X U A ⟶ LocalHomology.Cycles.relativeSingularChains X A :=
  cokernel.map
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (LocalHomology.Cycles.subspaceChainInclusion X A) (𝟙 _) (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A)
    (by
      rw [Category.id_comp]
      exact BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A)

/-- The small relative inclusion is induced by the actual absolute inclusion. -/
@[reassoc (attr := simp)]
theorem binarySmallRelativeInclusion_projection :
    binarySmallRelativeProjection X U A ≫ binarySmallRelativeInclusion X U A =
      BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A ≫ LocalHomology.Cycles.relativeChainProjection X A :=
  cokernel.π_desc _ _ _

/-- Comparison of the two actual short exact sequences, identical on `C(A)`. -/
def binarySmallRelativeSequenceMap :
    binarySmallRelativeSequence X U A ⟶ LocalHomology.Cycles.relativeChainSequence X A where
  τ₁ := 𝟙 _
  τ₂ := BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A
  τ₃ := binarySmallRelativeInclusion X U A
  comm₁₂ := by
    change 𝟙 _ ≫ LocalHomology.Cycles.subspaceChainInclusion X A =
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A) ≫
        BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A
    rw [Category.id_comp]
    exact (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A).symm
  comm₂₃ := (binarySmallRelativeInclusion_projection X U A).symm

/-- The relative comparison inherits a proved absolute small-chain
quasi-isomorphism by the homology sequences of these short exact sequences. -/
theorem binarySmallRelativeInclusion_quasiIso_of_small
    (hsmall : _root_.QuasiIso (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A)) :
    _root_.QuasiIso (binarySmallRelativeInclusion X U A) := by
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (binarySmallRelativeSequenceMap X U A)
    (binarySmallRelativeSequence_shortExact X U A)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (by change _root_.QuasiIso (𝟙 _); infer_instance) hsmall

/-- The canonical relative inclusion factors through the proved quotient
identification and the canonical small relative inclusion. -/
theorem relativeCoverInclusion_factor :
    relativeCoverCokernelMap X U A ≫ binarySmallRelativeInclusion X U A =
      relativeCoverInclusion X U A := by
  apply (cancel_epi
    (LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A))).mp
  rw [← Category.assoc, relativeCoverCokernelMap_projection, Category.assoc,
    binarySmallRelativeInclusion_projection, ← Category.assoc,
    BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left]
  exact (LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)).symm

/-- Relative excision follows from the actual absolute small-chain
quasi-isomorphism; the quotient identification is a chain isomorphism. -/
theorem relativeCoverInclusion_quasiIso_of_small
    (hsmall : _root_.QuasiIso (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A)) :
    _root_.QuasiIso (relativeCoverInclusion X U A) := by
  have := binarySmallRelativeInclusion_quasiIso_of_small X U A hsmall
  rw [← relativeCoverInclusion_factor]
  infer_instance

/-- For an actual binary open cover, the canonical inclusion of small relative
chains is a quasi-isomorphism. -/
theorem binarySmallRelativeInclusion_quasiIso
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) :
    _root_.QuasiIso (binarySmallRelativeInclusion X U A) :=
  binarySmallRelativeInclusion_quasiIso_of_small X U A
    (SmallSingularQuasiIso.Cycles.binarySmallIntegralChainInclusion_quasiIso X U A hU hA hcover)

/-- Relative excision for a binary open cover, proved for the actual inclusion
of pairs `(U, U ∩ A) → (X, A)`. -/
theorem relativeCoverInclusion_quasiIso
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) :
    _root_.QuasiIso (relativeCoverInclusion X U A) :=
  relativeCoverInclusion_quasiIso_of_small X U A
    (SmallSingularQuasiIso.Cycles.binarySmallIntegralChainInclusion_quasiIso X U A hU hA hcover)

/-- The relative homology isomorphism of a binary open cover is induced by
the genuine inclusion of pairs. -/
def relativeCoverHomologyIso
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) n ≅
      LocalHomology.Cycles.relativeSingularHomology X A n := by
  have := relativeCoverInclusion_quasiIso X U A hU hA hcover
  exact isoOfQuasiIsoAt (relativeCoverInclusion X U A) n

@[simp]
theorem relativeCoverHomologyIso_hom
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (n : ℕ) :
    (relativeCoverHomologyIso X U A hU hA hcover n).hom =
      HomologicalComplex.homologyMap (relativeCoverInclusion X U A) n := rfl

variable (x : X) (hx : x ∈ U)

/-- The actual map of punctured pairs induced by the inclusion of `U` into `X`. -/
def localExcisionChainMap :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ⟶
      LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X) :=
  LocalHomology.Cycles.relativeSingularChainsMap (LocalHomology.Cycles.subspaceInclusion X U) (by
    intro y hy
    change y.1 ≠ x
    change y ≠ (⟨x, hx⟩ : U) at hy
    exact fun h => hy (Subtype.ext h))

/-- The punctured subspace of `U` is the preimage of the ambient punctured space;
the relative-chain isomorphism is induced by the identity homeomorphism. -/
def localRelativePreimageIso :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ≅
      LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ({x}ᶜ : Set X)) :=
  LocalHomology.Cycles.relativeSingularChainsIso (Homeomorph.refl (TopCat.of U)) (by
    intro y
    change y ≠ (⟨x, hx⟩ : U) ↔ y.1 ≠ x
    exact not_congr Subtype.ext_iff)

/-- The punctured-subspace identification does not change absolute chains. -/
@[reassoc (attr := simp)]
theorem localRelativePreimageIso_projection :
    LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ≫
        (localRelativePreimageIso X U x hx).hom =
      LocalHomology.Cycles.relativeChainProjection (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ({x}ᶜ : Set X)) := by
  have h : Set.MapsTo (𝟙 (TopCat.of U)) ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ({x}ᶜ : Set X)) := by
    intro y hy
    change y.1 ≠ x
    change y ≠ (⟨x, hx⟩ : U) at hy
    exact fun h => hy (Subtype.ext h)
  change _ ≫ LocalHomology.Cycles.relativeSingularChainsMap (𝟙 (TopCat.of U)) h = _
  rw [LocalHomology.Cycles.relativeChainProjection_naturality, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Local excision is the relative-cover inclusion after the identity
identification of the two punctured-subspace presentations. -/
theorem localExcisionChainMap_factor :
    (localRelativePreimageIso X U x hx).hom ≫ relativeCoverInclusion X U ({x}ᶜ : Set X) =
      localExcisionChainMap X U x hx := by
  apply (cancel_epi
    (LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U))).mp
  rw [← Category.assoc, localRelativePreimageIso_projection]
  exact (LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)).trans
    (LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) _).symm

/-- Local excision: an open neighborhood of a point in a T1 space induces a
quasi-isomorphism on the actual punctured relative singular chain complexes. -/
theorem localExcisionChainMap_quasiIso [T1Space X] (hU : IsOpen U) :
    _root_.QuasiIso (localExcisionChainMap X U x hx) := by
  have hcover : U ∪ ({x}ᶜ : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · subst y
      exact Or.inl hx
    · exact Or.inr (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy)
  have := relativeCoverInclusion_quasiIso X U ({x}ᶜ : Set X)
    hU isOpen_compl_singleton hcover
  rw [← localExcisionChainMap_factor X U x hx]
  infer_instance

/-- The canonical local homology isomorphism induced by an open-neighborhood
inclusion, with no excision or local-orientation assumption. -/
def localExcisionHomologyIso [T1Space X] (hU : IsOpen U) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of U) (⟨x, hx⟩ : U) n ≅
      LocalHomology.Cycles.localSingularHomology X x n := by
  have := localExcisionChainMap_quasiIso X U x hx hU
  exact isoOfQuasiIsoAt (localExcisionChainMap X U x hx) n

@[simp]
theorem localExcisionHomologyIso_hom [T1Space X] (hU : IsOpen U) (n : ℕ) :
    (localExcisionHomologyIso X U x hx hU n).hom =
      HomologicalComplex.homologyMap (localExcisionChainMap X U x hx) n := rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
