import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Compact Support Assembly -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles

noncomputable section

/-!
# Actual Mayer--Vietoris assembly for compact supports

The restriction maps below are induced by identity maps of complementary
pairs. The binary gluing and detection results follow from the proved
relative Mayer--Vietoris sequence. They are generic statements about actual
relative homology; no orientation or fundamental class is supplied as an axiom.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0})

/-- The actual restriction from a larger support set to a smaller one. -/
def homologyWithSupportRestriction {K L : Set X} (hKL : K ⊆ L) (n : ℕ) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport X L n ⟶ HomologyWithSupports.Cycles.singularHomologyWithSupport X K n :=
  HomologicalComplex.homologyMap (LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction X hKL) n

@[simp]
theorem homologyWithSupportRestriction_refl (K : Set X) (n : ℕ) :
    homologyWithSupportRestriction X (Set.Subset.refl K) n = 𝟙 _ := by
  unfold homologyWithSupportRestriction
  rw [LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_refl, HomologicalComplex.homologyMap_id]

@[reassoc]
theorem homologyWithSupportRestriction_trans {K L P : Set X}
    (hKL : K ⊆ L) (hLP : L ⊆ P) (n : ℕ) :
    homologyWithSupportRestriction X hLP n ≫ homologyWithSupportRestriction X hKL n =
      homologyWithSupportRestriction X (hKL.trans hLP) n := by
  unfold homologyWithSupportRestriction
  rw [← HomologicalComplex.homologyMap_comp, LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_trans]

/-- Restricting the support does not change the subsequent local class. -/
@[reassoc]
theorem homologyWithSupportRestriction_toPoint {K L : Set X} (hKL : K ⊆ L)
    (x : X) (hx : x ∈ K) (n : ℕ) :
    homologyWithSupportRestriction X hKL n ≫ LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x (hKL hx) n := by
  unfold homologyWithSupportRestriction LocalHomologyPresheaf.Cycles.localHomologyToPoint
  rw [← HomologicalComplex.homologyMap_comp, LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction_toPoint]

/-- Empty support gives zero actual relative homology in every degree. -/
theorem homologyWithSupport_empty_isZero (n : ℕ) :
    IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X ∅ n) := by
  let : IsIso (LocalHomology.Cycles.subspaceInclusion X Set.univ) := by
    change IsIso ((TopCat.isoOfHomeo (X := TopCat.of (Set.univ : Set X)) (Y := X)
      (Homeomorph.Set.univ X)).hom)
    infer_instance
  let : IsIso (LocalHomology.Cycles.subspaceChainInclusion X Set.univ) := by
    dsimp only [LocalHomology.Cycles.subspaceChainInclusion]
    infer_instance
  have hz := isZero_cokernel_of_epi (LocalHomology.Cycles.subspaceChainInclusion X Set.univ)
  have hh := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ)
    (ComplexShape.down ℕ) n).map_isZero hz
  change IsZero (LocalHomology.Cycles.relativeSingularHomology X Set.univ n) at hh
  simpa only [HomologyWithSupports.Cycles.singularHomologyWithSupport, Set.compl_empty] using! hh

private theorem moduleBiprod_ext (M N : ModuleCat.{0} ℤ)
    (a b : (M ⊞ N : ModuleCat.{0} ℤ))
    (hf : (biprod.fst : M ⊞ N ⟶ M) a = (biprod.fst : M ⊞ N ⟶ M) b)
    (hs : (biprod.snd : M ⊞ N ⟶ N) a = (biprod.snd : M ⊞ N ⟶ N) b) : a = b := by
  have ha := ConcreteCategory.congr_hom (biprod.total (X := M) (Y := N)) a
  have hb := ConcreteCategory.congr_hom (biprod.total (X := M) (Y := N)) b
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) a) +
    (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) a) = a at ha
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) b) +
    (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) b) = b at hb
  rw [hf, hs] at ha
  exact ha.symm.trans hb

private theorem relativeMayerVietorisFirst_injective (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (hUnion : IsZero (LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (n + 1))) :
    Function.Injective (HomologyWithSupports.Cycles.relativeMayerVietorisFirst X A B n).hom := by
  apply (injective_iff_map_eq_zero (HomologyWithSupports.Cycles.relativeMayerVietorisFirst X A B n).hom).2
  intro z hz
  have hmem : z ∈ LinearMap.ker (HomologyWithSupports.Cycles.relativeMayerVietorisFirst X A B n).hom := hz
  rw [← HomologyWithSupports.Cycles.relativeMayerVietoris_range_boundary X A B hA hB n] at hmem
  obtain ⟨b, rfl⟩ := hmem
  have hb : b = 0 := (ModuleCat.isZero_iff_subsingleton.mp hUnion).elim _ _
  rw [hb, map_zero]

private theorem relativeMayerVietoris_ext (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (hUnion : IsZero (LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (n + 1))) :
    ∀ a b : LocalHomology.Cycles.relativeSingularHomology X (A ∩ B) n,
      (HomologicalComplex.homologyMap
        (HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_left : A ∩ B ⊆ A)) n) a =
        (HomologicalComplex.homologyMap
          (HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_left : A ∩ B ⊆ A)) n) b →
      (HomologicalComplex.homologyMap
        (HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_right : A ∩ B ⊆ B)) n) a =
        (HomologicalComplex.homologyMap
          (HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_right : A ∩ B ⊆ B)) n) b → a = b := by
  intro a b ha hb
  apply relativeMayerVietorisFirst_injective X A B hA hB n hUnion
  apply moduleBiprod_ext
  · exact (ConcreteCategory.congr_hom (HomologyWithSupports.Cycles.relativeMayerVietorisFirst_fst X A B n) a).trans
      (ha.trans (ConcreteCategory.congr_hom
        (HomologyWithSupports.Cycles.relativeMayerVietorisFirst_fst X A B n) b).symm)
  · exact (ConcreteCategory.congr_hom (HomologyWithSupports.Cycles.relativeMayerVietorisFirst_snd X A B n) a).trans
      ((congrArg Neg.neg hb).trans (ConcreteCategory.congr_hom
        (HomologyWithSupports.Cycles.relativeMayerVietorisFirst_snd X A B n) b).symm)

private theorem relativeMayerVietoris_ext_of_eq (A B U : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (hUnion : IsZero (LocalHomology.Cycles.relativeSingularHomology X (A ∪ B) (n + 1)))
    (hU : U = A ∩ B) (hUA : U ⊆ A) (hUB : U ⊆ B) :
    ∀ a b : LocalHomology.Cycles.relativeSingularHomology X U n,
      (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hUA) n) a =
        (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hUA) n) b →
      (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hUB) n) a =
        (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hUB) n) b → a = b := by
  subst U
  exact relativeMayerVietoris_ext X A B hA hB n hUnion

/-- The two restrictions detect a class on a union when the next homology
group of the intersection vanishes. -/
theorem supportUnion_ext (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (hInt : IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∩ L) (n + 1))) :
    ∀ a b : HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∪ L) n,
      homologyWithSupportRestriction X (Set.subset_union_left : K ⊆ K ∪ L) n a =
        homologyWithSupportRestriction X (Set.subset_union_left : K ⊆ K ∪ L) n b →
      homologyWithSupportRestriction X (Set.subset_union_right : L ⊆ K ∪ L) n a =
        homologyWithSupportRestriction X (Set.subset_union_right : L ⊆ K ∪ L) n b → a = b := by
  have hI : IsZero (LocalHomology.Cycles.relativeSingularHomology X (Kᶜ ∪ Lᶜ) (n + 1)) := by
    simpa only [HomologyWithSupports.Cycles.singularHomologyWithSupport, Set.compl_inter] using hInt
  let hUK : (K ∪ L)ᶜ ⊆ Kᶜ := fun _ hx h => hx (Or.inl h)
  let hUL : (K ∪ L)ᶜ ⊆ Lᶜ := fun _ hx h => hx (Or.inr h)
  have h := relativeMayerVietoris_ext_of_eq X Kᶜ Lᶜ (K ∪ L)ᶜ
    hK.isOpen_compl hL.isOpen_compl n hI (Set.compl_union K L) hUK hUL
  simpa only [HomologyWithSupports.Cycles.singularHomologyWithSupport, homologyWithSupportRestriction,
    LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction, HomologyWithSupports.Cycles.relativeSubsetChainMap] using h

/-- Mayer--Vietoris propagates vanishing from two supports and the next
homology group of their intersection to their union. -/
theorem supportUnion_isZero (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (hKn : IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X K n))
    (hLn : IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X L n))
    (hInt : IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∩ L) (n + 1))) :
    IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∪ L) n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let : Subsingleton (HomologyWithSupports.Cycles.singularHomologyWithSupport X K n) :=
    ModuleCat.isZero_iff_subsingleton.mp hKn
  let : Subsingleton (HomologyWithSupports.Cycles.singularHomologyWithSupport X L n) :=
    ModuleCat.isZero_iff_subsingleton.mp hLn
  exact ⟨fun a b => supportUnion_ext X K L hK hL n hInt a b
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

private theorem relativeMayerVietoris_glue_of_eq (A B U V : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (hU : U = A ∩ B) (hV : V = A ∪ B)
    (hUA : U ⊆ A) (hUB : U ⊆ B) (hAV : A ⊆ V) (hBV : B ⊆ V) :
    ∀ (a : LocalHomology.Cycles.relativeSingularHomology X A n) (b : LocalHomology.Cycles.relativeSingularHomology X B n),
      (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hAV) n) a =
        (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hBV) n) b →
      ∃ c : LocalHomology.Cycles.relativeSingularHomology X U n,
        (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hUA) n) c = a ∧
        (HomologicalComplex.homologyMap (HomologyWithSupports.Cycles.relativeSubsetChainMap X hUB) n) c = b := by
  subst U
  subst V
  exact HomologyWithSupports.Cycles.relativeMayerVietoris_glue X A B hA hB n

/-- Compatible classes on closed supports glue to an actual relative
homology class supported on their union. -/
theorem supportUnion_glue (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    ∀ (a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K n) (b : HomologyWithSupports.Cycles.singularHomologyWithSupport X L n),
      homologyWithSupportRestriction X (Set.inter_subset_left : K ∩ L ⊆ K) n a =
        homologyWithSupportRestriction X (Set.inter_subset_right : K ∩ L ⊆ L) n b →
      ∃ c : HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∪ L) n,
        homologyWithSupportRestriction X (Set.subset_union_left : K ⊆ K ∪ L) n c = a ∧
        homologyWithSupportRestriction X (Set.subset_union_right : L ⊆ K ∪ L) n c = b := by
  let hUA : (K ∪ L)ᶜ ⊆ Kᶜ := fun _ hx h => hx (Or.inl h)
  let hUB : (K ∪ L)ᶜ ⊆ Lᶜ := fun _ hx h => hx (Or.inr h)
  let hAV : Kᶜ ⊆ (K ∩ L)ᶜ := fun _ hx h => hx h.1
  let hBV : Lᶜ ⊆ (K ∩ L)ᶜ := fun _ hx h => hx h.2
  have h := relativeMayerVietoris_glue_of_eq X Kᶜ Lᶜ (K ∪ L)ᶜ (K ∩ L)ᶜ
    hK.isOpen_compl hL.isOpen_compl n (Set.compl_union K L) (Set.compl_inter K L)
    hUA hUB hAV hBV
  simpa only [HomologyWithSupports.Cycles.singularHomologyWithSupport, homologyWithSupportRestriction,
    LocalHomologyPresheaf.Cycles.relativeComplementChainRestriction, HomologyWithSupports.Cycles.relativeSubsetChainMap] using h

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles
