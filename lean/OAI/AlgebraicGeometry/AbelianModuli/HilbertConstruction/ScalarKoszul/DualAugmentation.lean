import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.LowestTerm
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.DualCokernelResidue

/-! # Dual Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.DualAugmentation

noncomputable section

/-! The dual of the first Koszul differential has image exactly the parameter ideal, so its cokernel is the parameter quotient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

theorem scalarKoszulFirstMap_snd (M : ModuleCat.{u} R) (r : R) (rs : List R) (m : M) :
    (mappingCone.snd (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs))).v
      (LowestTerm.scalarKoszulLowestIndex rs) (LowestTerm.scalarKoszulLowestIndex rs) (add_zero _)
        (LowestTerm.scalarKoszulFirstMap M (r :: rs) m) = r • (LowestTerm.scalarKoszulLowestTermIso M rs).inv m := by
  let f := r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)
  let i := LowestTerm.scalarKoszulLowestIndex rs
  let k := LowestTerm.scalarKoszulNextIndex rs
  have hik : i + 1 = k := LowestTerm.scalarKoszulLowestIndex_add_one rs
  have h₁ := ConcreteCategory.congr_hom (mappingCone.inr_f_snd_v f i)
    ((LowestTerm.scalarKoszulLowestTermIso M rs).inv m)
  have h₂ := ConcreteCategory.congr_hom (mappingCone.inl_v_snd_v f k i (by omega))
    (LowestTerm.scalarKoszulFirstMap M rs m)
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h₁ h₂
  rw [LowestTerm.scalarKoszulFirstMap_cons, map_sub, map_smul, h₁, h₂, sub_zero]

theorem scalarKoszulFirstMap_fst (M : ModuleCat.{u} R) (r : R) (rs : List R) (m : M) :
    (mappingCone.fst (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs))).1.v
      (LowestTerm.scalarKoszulLowestIndex rs) (LowestTerm.scalarKoszulNextIndex rs) (LowestTerm.scalarKoszulLowestIndex_add_one rs)
        (LowestTerm.scalarKoszulFirstMap M (r :: rs) m) = -LowestTerm.scalarKoszulFirstMap M rs m := by
  let f := r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)
  let i := LowestTerm.scalarKoszulLowestIndex rs
  let k := LowestTerm.scalarKoszulNextIndex rs
  have hik : i + 1 = k := LowestTerm.scalarKoszulLowestIndex_add_one rs
  have h₁ := ConcreteCategory.congr_hom (mappingCone.inr_f_fst_v f i k hik)
    ((LowestTerm.scalarKoszulLowestTermIso M rs).inv m)
  have h₂ := ConcreteCategory.congr_hom (mappingCone.inl_v_fst_v f k i hik)
    (LowestTerm.scalarKoszulFirstMap M rs m)
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h₁ h₂
  rw [LowestTerm.scalarKoszulFirstMap_cons, map_sub, map_smul, h₁, h₂, smul_zero, zero_sub]

def scalarKoszulFirstDualMap (rs : List R) :
    Module.Dual R ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).X (LowestTerm.scalarKoszulNextIndex rs)) →ₗ[R] R :=
  RankOneDualPresentation.rankOneDualCoefficientMap (LowestTerm.scalarKoszulLowestTermIso (ModuleCat.of R R) rs).symm.toLinearEquiv
    ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).d (LowestTerm.scalarKoszulLowestIndex rs) (LowestTerm.scalarKoszulNextIndex rs)).hom

theorem scalarKoszulFirstDualMap_range (rs : List R) :
    (scalarKoszulFirstDualMap rs).range = Regular.SequenceBasic.Ideal.ofList rs := by
  induction rs with
  | nil =>
    have : Subsingleton ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) []).X (LowestTerm.scalarKoszulNextIndex ([] : List R))) :=
      ModuleCat.subsingleton_of_isZero (KoszulComplex.scalarKoszulComplex_isZero_X _ [] 1 (Or.inr (by decide)))
    have hz : scalarKoszulFirstDualMap ([] : List R) = 0 := by
      apply LinearMap.ext
      intro ℓ
      change ℓ (LowestTerm.scalarKoszulFirstMap (ModuleCat.of R R) [] 1) = 0
      rw [Subsingleton.elim (LowestTerm.scalarKoszulFirstMap (ModuleCat.of R R) [] 1) 0, map_zero]
    rw [hz, LinearMap.range_zero, Regular.SequenceBasic.Ideal.ofList_nil]
  | cons r rs ih =>
    let M := ModuleCat.of R R
    let C := KoszulComplex.scalarKoszulComplex M rs
    let E := LowestTerm.scalarKoszulLowestTermIso M rs
    let i := LowestTerm.scalarKoszulLowestIndex rs
    let k := LowestTerm.scalarKoszulNextIndex rs
    let f := r • 𝟙 C
    have hik : i + 1 = k := LowestTerm.scalarKoszulLowestIndex_add_one rs
    apply le_antisymm
    · rintro x ⟨ℓ, rfl⟩
      change ℓ (LowestTerm.scalarKoszulFirstMap M (r :: rs) 1) ∈ Regular.SequenceBasic.Ideal.ofList (r :: rs)
      rw [LowestTerm.scalarKoszulFirstMap_cons, map_sub, map_smul]
      apply Ideal.sub_mem
      · have hr : r ∈ Regular.SequenceBasic.Ideal.ofList (r :: rs) := Ideal.subset_span (by simp)
        exact (Regular.SequenceBasic.Ideal.ofList (r :: rs)).mul_mem_right _ hr
      · have hle : Regular.SequenceBasic.Ideal.ofList rs ≤ Regular.SequenceBasic.Ideal.ofList (r :: rs) := by
          rw [Regular.SequenceBasic.Ideal.ofList_cons]
          exact le_sup_right
        apply hle
        have hm := LinearMap.mem_range_self (scalarKoszulFirstDualMap rs)
          (ℓ.comp ((mappingCone.inl f).v k i (by omega)).hom)
        rw [ih] at hm
        exact hm
    · rw [Regular.SequenceBasic.Ideal.ofList_cons]
      apply sup_le
      · apply Ideal.span_le.mpr
        intro x hx
        have hxr : x = r := Set.mem_singleton_iff.mp hx
        subst x
        let ℓ := E.hom.hom.comp ((mappingCone.snd f).v i i (add_zero i)).hom
        refine ⟨ℓ, ?_⟩
        change E.hom ((mappingCone.snd f).v i i (add_zero i)
          (LowestTerm.scalarKoszulFirstMap M (r :: rs) 1)) = r
        rw [scalarKoszulFirstMap_snd, E.hom.hom.map_smul]
        have he : E.hom (E.inv 1) = 1 := ConcreteCategory.congr_hom E.inv_hom_id 1
        rw [he]
        exact mul_one r
      · rw [← ih]
        rintro x ⟨ℓ, hx⟩
        let ℓ' := -(ℓ.comp ((mappingCone.fst f).1.v i k hik).hom)
        refine ⟨ℓ', ?_⟩
        change -ℓ ((mappingCone.fst f).1.v i k hik (LowestTerm.scalarKoszulFirstMap M (r :: rs) 1)) = x
        rw [scalarKoszulFirstMap_fst, map_neg, neg_neg]
        exact hx

def scalarKoszulDualCokernelQuotientIso (rs : List R) :
    cokernel (ModuleCat.ofHom
      ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).d
        (LowestTerm.scalarKoszulLowestIndex rs) (LowestTerm.scalarKoszulNextIndex rs)).hom.dualMap) ≅
      ModuleCat.of R (R ⧸ Regular.SequenceBasic.Ideal.ofList rs) := by
  let C := KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs
  let f := (C.d (LowestTerm.scalarKoszulLowestIndex rs) (LowestTerm.scalarKoszulNextIndex rs)).hom
  let E := Minimal.DualCokernelResidue.rankOneDualEquiv (LowestTerm.scalarKoszulLowestTermIso (ModuleCat.of R R) rs).symm.toLinearEquiv
  have hmap : f.dualMap.range.map E.toLinearMap = Regular.SequenceBasic.Ideal.ofList rs := by
    rw [← LinearMap.range_comp]
    exact scalarKoszulFirstDualMap_range rs
  exact ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom f.dualMap) ≪≫
    (Submodule.Quotient.equiv f.dualMap.range (Regular.SequenceBasic.Ideal.ofList rs) E hmap).toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.DualAugmentation
