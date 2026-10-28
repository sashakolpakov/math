import OAI.AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.SupportMayerVietorisNaturality

/-! # Cohomology Mayer Vietoris Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CohomologyMayerVietorisNaturality

noncomputable section

/-!
# Naturality of rational support Mayer--Vietoris

The maps below are induced by the already constructed maps of actual binary
small-chain quotients. Naturality of the connecting homomorphism is obtained
from the native homology-sequence theorem, and then transported through the
proved rational-duality and subdivision comparisons.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) {A B A' B' : Set X}

/-- Dualizing the actual map of binary small-chain sequences reverses its direction. -/
def binaryRelativeDualSequenceMap (hA : A ⊆ A') (hB : B ⊆ B') :
    SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A' B' ⟶ SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B :=
  RelativeCochainDual.rationalChainDualFunctor.mapShortComplex.map
    (ShortComplex.opMap (SupportMayerVietorisNaturality.binaryRelativeChainSequenceMap X hA hB))

@[simp]
theorem binaryRelativeDualSequenceMap_τ₁ (hA : A ⊆ A') (hB : B ⊆ B') :
    (binaryRelativeDualSequenceMap X hA hB).τ₁ =
      RelativeCochainDual.rationalChainDualMap (SupportMayerVietorisNaturality.binarySmallComplementMap X hA hB) := rfl

@[simp]
theorem binaryRelativeDualSequenceMap_τ₃ (hA : A ⊆ A') (hB : B ⊆ B') :
    (binaryRelativeDualSequenceMap X hA hB).τ₃ =
      RelativeCochainDual.rationalChainDualMap
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB)) := rfl

/-- Naturality before transporting from the genuine dual short exact sequence. -/
@[reassoc]
theorem binaryRelativeDualSequence_δ_naturality
    (hA : A ⊆ A') (hB : B ⊆ B') (n : ℕ) :
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A' B').δ n (n + 1) rfl ≫
      HomologicalComplex.homologyMap
        (RelativeCochainDual.rationalChainDualMap (SupportMayerVietorisNaturality.binarySmallComplementMap X hA hB)) (n + 1) =
    HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB))) n ≫
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A B).δ n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (binaryRelativeDualSequenceMap X hA hB)
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A' B')
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A B) n (n + 1) rfl

@[reassoc]
theorem relativeRationalSubsetCohomologyMap_dual_naturality
    {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X h n) ≫
        (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X S n).hom =
      (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X T n).hom ≫
        HomologicalComplex.homologyMap
          (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X h)) n :=
  SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso_naturality (𝟙 X) (fun _ hx => h hx) n

/-- Naturality of the inverse union comparison uses the actual small-quotient square. -/
@[reassoc]
theorem binaryRelativeDualFirstHomologyIso_inv_naturality
    (hA : A ⊆ A') (hB : B ⊆ B')
    (oA : IsOpen A) (oB : IsOpen B) (oA' : IsOpen A') (oB' : IsOpen B') (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.union_subset_union hA hB) n) ≫
        (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B oA oB n).inv =
      (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A' B' oA' oB' n).inv ≫
        HomologicalComplex.homologyMap
          (RelativeCochainDual.rationalChainDualMap (SupportMayerVietorisNaturality.binarySmallComplementMap X hA hB)) n := by
  simp only [SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso_inv]
  rw [← Category.assoc, relativeRationalSubsetCohomologyMap_dual_naturality]
  have hs := congrArg (fun f => HomologicalComplex.homologyMap
    (RelativeCochainDual.rationalChainDualMap f) n) (SupportMayerVietorisNaturality.binarySmallComplementToRelative_naturality X hA hB)
  simp only [RelativeCochainDual.rationalChainDualMap_comp, HomologicalComplex.homologyMap_comp] at hs
  simpa only [Category.assoc] using congrArg
    (fun f => (SupportCohomologyMayerVietoris.relativeRationalCohomologyDualIso X (A' ∪ B') n).hom ≫ f) hs.symm

/-- Naturality of the union comparison in the forward direction. -/
@[reassoc]
theorem binaryRelativeDualFirstHomologyIso_hom_naturality
    (hA : A ⊆ A') (hB : B ⊆ B')
    (oA : IsOpen A) (oB : IsOpen B) (oA' : IsOpen A') (oB' : IsOpen B') (n : ℕ) :
    (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A' B' oA' oB' n).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.union_subset_union hA hB) n) =
      HomologicalComplex.homologyMap
          (RelativeCochainDual.rationalChainDualMap (SupportMayerVietorisNaturality.binarySmallComplementMap X hA hB)) n ≫
        (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B oA oB n).hom := by
  apply (cancel_mono (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B oA oB n).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [binaryRelativeDualFirstHomologyIso_inv_naturality X hA hB oA oB oA' oB' n,
    Iso.hom_inv_id_assoc]

@[reassoc]
theorem binaryRelativeDualThirdHomologyIso_inv_naturality
    (hA : A ⊆ A') (hB : B ⊆ B') (n : ℕ) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.inter_subset_inter hA hB) n) ≫
        (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A B n).inv =
      (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A' B' n).inv ≫
        HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
          (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB))) n :=
  relativeRationalSubsetCohomologyMap_dual_naturality X
    (Set.inter_subset_inter hA hB) n

/-- The actual relative rational connecting maps commute with restriction of pairs. -/
@[reassoc]
theorem relativeRationalMayerVietorisBoundary_naturality
    (hA : A ⊆ A') (hB : B ⊆ B')
    (oA : IsOpen A) (oB : IsOpen B) (oA' : IsOpen A') (oB' : IsOpen B') (n : ℕ) :
    SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.inter_subset_inter hA hB) n ≫
        SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A B oA oB n =
      SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary X A' B' oA' oB' n ≫
        SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.union_subset_union hA hB) (n + 1) := by
  apply (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map_injective
  simp only [Functor.map_comp, SupportCohomologyMayerVietoris.relativeRationalMayerVietorisBoundary_forget, Category.assoc]
  rw [binaryRelativeDualThirdHomologyIso_inv_naturality_assoc X hA hB n]
  rw [binaryRelativeDualFirstHomologyIso_hom_naturality X hA hB oA oB oA' oB' (n + 1)]
  change (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A' B' n).inv ≫
      HomologicalComplex.homologyMap (RelativeCochainDual.rationalChainDualMap
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB))) n ≫
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A B).δ n (n + 1) rfl ≫
      (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B oA oB (n + 1)).hom =
    (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A' B' n).inv ≫
      (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A' B').δ n (n + 1) rfl ≫
      HomologicalComplex.homologyMap
        (RelativeCochainDual.rationalChainDualMap (SupportMayerVietorisNaturality.binarySmallComplementMap X hA hB)) (n + 1) ≫
      (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B oA oB (n + 1)).hom
  have hd := congrArg
    (fun f => (SupportCohomologyMayerVietoris.binaryRelativeDualThirdHomologyIso X A' B' n).inv ≫ f ≫
      (SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso X A B oA oB (n + 1)).hom)
    (binaryRelativeDualSequence_δ_naturality X hA hB n).symm
  simpa only [Category.assoc] using hd

/-- Equality of relative subspaces is compatible with the actual pair maps. -/
@[reassoc]
theorem relativeRationalCohomologyCongr_naturality
    {S T S' T' : Set X} (eS : S = S') (eT : T = T')
    (h : S ⊆ T) (h' : S' ⊆ T') (n : ℕ) :
    SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X h n ≫
        (SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X eS n).hom =
      (SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X eT n).hom ≫
        SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X h' n := by
  subst S'
  subst T'
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The complement identification for a union commutes with enlarging supports. -/
@[reassoc]
theorem supportUnionCohomologyIso_naturality
    {K L K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L') (n : ℕ) :
    SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.inter_subset_inter
        (Set.compl_subset_compl_of_subset hK) (Set.compl_subset_compl_of_subset hL)) n ≫
        (SupportCohomologyMayerVietoris.supportUnionCohomologyIso X K' L' n).hom =
      (SupportCohomologyMayerVietoris.supportUnionCohomologyIso X K L n).hom ≫
        SupportCohomologyMayerVietoris.supportCohomologyEnlargement X (Set.union_subset_union hK hL) n :=
  relativeRationalCohomologyCongr_naturality X
    (Set.compl_union K' L').symm (Set.compl_union K L).symm
    (Set.inter_subset_inter
      (Set.compl_subset_compl_of_subset hK) (Set.compl_subset_compl_of_subset hL))
    (Set.compl_subset_compl_of_subset (Set.union_subset_union hK hL)) n

/-- The complement identification for an intersection commutes with support enlargement. -/
@[reassoc]
theorem supportIntersectionCohomologyIso_naturality
    {K L K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L') (n : ℕ) :
    SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.union_subset_union
        (Set.compl_subset_compl_of_subset hK) (Set.compl_subset_compl_of_subset hL)) n ≫
        (SupportCohomologyMayerVietoris.supportIntersectionCohomologyIso X K' L' n).hom =
      (SupportCohomologyMayerVietoris.supportIntersectionCohomologyIso X K L n).hom ≫
        SupportCohomologyMayerVietoris.supportCohomologyEnlargement X (Set.inter_subset_inter hK hL) n :=
  relativeRationalCohomologyCongr_naturality X
    (Set.compl_inter K' L').symm (Set.compl_inter K L).symm
    (Set.union_subset_union
      (Set.compl_subset_compl_of_subset hK) (Set.compl_subset_compl_of_subset hL))
    (Set.compl_subset_compl_of_subset (Set.inter_subset_inter hK hL)) n

/-- The genuine support connecting homomorphism commutes with enlarging either support. -/
@[reassoc]
theorem supportCohomologyMayerVietorisBoundary_naturality
    {K L K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L')
    (cK : IsClosed K) (cL : IsClosed L) (cK' : IsClosed K') (cL' : IsClosed L') (n : ℕ) :
    SupportCohomologyMayerVietoris.supportCohomologyEnlargement X (Set.union_subset_union hK hL) n ≫
        SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X K' L' cK' cL' n =
      SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X K L cK cL n ≫
        SupportCohomologyMayerVietoris.supportCohomologyEnlargement X (Set.inter_subset_inter hK hL) (n + 1) := by
  apply (cancel_epi (SupportCohomologyMayerVietoris.supportUnionCohomologyIso X K L n).hom).1
  simp only [SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary, Category.assoc]
  rw [← supportUnionCohomologyIso_naturality_assoc X hK hL n,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc,
    ← supportIntersectionCohomologyIso_naturality X hK hL (n + 1)]
  have hn := congrArg
    (fun f => f ≫ (SupportCohomologyMayerVietoris.supportIntersectionCohomologyIso X K' L' (n + 1)).hom)
    (relativeRationalMayerVietorisBoundary_naturality X
      (Set.compl_subset_compl_of_subset hK) (Set.compl_subset_compl_of_subset hL)
      cK'.isOpen_compl cL'.isOpen_compl cK.isOpen_compl cL.isOpen_compl n)
  simpa only [Category.assoc] using hn

/-- The actual rational relative Mayer--Vietoris sequence starts injectively in degree zero. -/
theorem relativeRationalMayerVietorisFirst_zero_mono
    (A B : Set X) (oA : IsOpen A) (oB : IsOpen B) :
    Mono (SupportCohomologyMayerVietoris.relativeRationalMayerVietorisFirst X A B 0) := by
  have : Mono (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).f :=
    (SupportCohomologyMayerVietoris.binaryRelativeDualSequence_shortExact X A B).mono_f
  have : Mono (HomologicalComplex.homologyMap (SupportCohomologyMayerVietoris.binaryRelativeDualSequence X A B).f 0) := by
    apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    intro i hi
    exact Nat.succ_ne_zero i hi
  have : Mono ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
      (SupportCohomologyMayerVietoris.relativeRationalMayerVietorisFirst X A B 0)) := by
    rw [← SupportCohomologyMayerVietoris.binaryRelativeDualFirstHomologyIso_first X A B oA oB 0]
    infer_instance
  exact (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mono_of_mono_map inferInstance

/-- The actual support sequence starts injectively; this includes every compact stage. -/
theorem supportCohomologyMayerVietorisFirst_zero_mono
    (K L : Set X) (cK : IsClosed K) (cL : IsClosed L) :
    Mono (SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisFirst X K L 0) := by
  have := relativeRationalMayerVietorisFirst_zero_mono X Kᶜ Lᶜ
    cK.isOpen_compl cL.isOpen_compl
  have he : SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisFirst X K L 0 =
      (SupportCohomologyMayerVietoris.supportIntersectionCohomologyIso X K L 0).inv ≫
        SupportCohomologyMayerVietoris.relativeRationalMayerVietorisFirst X Kᶜ Lᶜ 0 := by
    rw [SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisFirst_comparison, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end

end OAI.AlgebraicTopology.Duality.Poincare.CohomologyMayerVietorisNaturality
