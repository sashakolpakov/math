import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.FiniteTerms

/-! # Lowest Term -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.LowestTerm

noncomputable section

/-! The lowest Koszul term is the coefficient module. Its first differential has the explicit recursive form consisting of minus the previous differential and multiplication by the new parameter. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CochainComplex
universe u
variable {R : Type u} [CommRing R]

def scalarKoszulLowestIndex : List R → ℤ
  | [] => 0
  | _ :: rs => scalarKoszulLowestIndex rs - 1

def scalarKoszulNextIndex : List R → ℤ
  | [] => 1
  | _ :: rs => LowestTerm.scalarKoszulLowestIndex rs

omit [CommRing R] in
theorem scalarKoszulLowestIndex_eq_neg_length (rs : List R) :
    LowestTerm.scalarKoszulLowestIndex rs = -(rs.length : ℤ) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [LowestTerm.scalarKoszulLowestIndex, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
    omega

omit [CommRing R] in
theorem scalarKoszulLowestIndex_add_one (rs : List R) :
    LowestTerm.scalarKoszulLowestIndex rs + 1 = scalarKoszulNextIndex rs := by
  cases rs <;> simp [LowestTerm.scalarKoszulLowestIndex, scalarKoszulNextIndex]

def mappingConeFstIsoOfZeroCurrent (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : C ⟶ C) (i j : ℤ) (hij : i + 1 = j) (hz : IsZero (C.X i)) :
    (mappingCone f).X i ≅ C.X j where
  hom := (mappingCone.fst f).1.v i j hij
  inv := (mappingCone.inl f).v j i (by omega)
  hom_inv_id := by
    have hs : (mappingCone.snd f).v i i (add_zero i) = 0 := hz.eq_of_tgt _ _
    have h := mappingCone.id_X f i j hij
    rw [hs, zero_comp, add_zero] at h
    exact h
  inv_hom_id := mappingCone.inl_v_fst_v f j i hij

def scalarKoszulLowestTermIso (M : ModuleCat.{u} R) :
    ∀ rs : List R, (KoszulComplex.scalarKoszulComplex M rs).X (LowestTerm.scalarKoszulLowestIndex rs) ≅ M
  | [] => HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  | r :: rs => by
    let i := LowestTerm.scalarKoszulLowestIndex rs
    have hz : IsZero ((KoszulComplex.scalarKoszulComplex M rs).X (i - 1)) := by
      apply KoszulComplex.scalarKoszulComplex_isZero_X M rs
      apply Or.inl
      have hi := scalarKoszulLowestIndex_eq_neg_length rs
      dsimp only [i]
      omega
    exact mappingConeFstIsoOfZeroCurrent (KoszulComplex.scalarKoszulComplex M rs)
      (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs)) (i - 1) i (by omega) hz ≪≫ scalarKoszulLowestTermIso M rs

def scalarKoszulFirstMap (M : ModuleCat.{u} R) (rs : List R) :
    M →ₗ[R] (KoszulComplex.scalarKoszulComplex M rs).X (scalarKoszulNextIndex rs) :=
  ((KoszulComplex.scalarKoszulComplex M rs).d (LowestTerm.scalarKoszulLowestIndex rs) (scalarKoszulNextIndex rs)).hom.comp
    (LowestTerm.scalarKoszulLowestTermIso M rs).inv.hom

theorem scalarKoszulFirstMap_cons (M : ModuleCat.{u} R) (r : R) (rs : List R) (m : M) :
    scalarKoszulFirstMap M (r :: rs) m =
      r • (mappingCone.inr (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs))).f (LowestTerm.scalarKoszulLowestIndex rs)
        ((LowestTerm.scalarKoszulLowestTermIso M rs).inv m) -
      (mappingCone.inl (r • 𝟙 (KoszulComplex.scalarKoszulComplex M rs))).v
        (scalarKoszulNextIndex rs) (LowestTerm.scalarKoszulLowestIndex rs)
        (by have h := scalarKoszulLowestIndex_add_one rs; omega) (scalarKoszulFirstMap M rs m) := by
  let C := KoszulComplex.scalarKoszulComplex M rs
  let f := r • 𝟙 C
  let E := LowestTerm.scalarKoszulLowestTermIso M rs
  let i := LowestTerm.scalarKoszulLowestIndex rs
  let k := scalarKoszulNextIndex rs
  have hik : i + 1 = k := scalarKoszulLowestIndex_add_one rs
  have h := congrArg (fun a => E.inv ≫ a)
    (mappingCone.inl_v_d f i (i - 1) k (by omega) (by omega))
  rw [Preadditive.comp_sub] at h
  have hm := ConcreteCategory.congr_hom h m
  change scalarKoszulFirstMap M (r :: rs) m =
    (mappingCone.inr f).f i (r • E.inv m) -
      (mappingCone.inl f).v k i (by omega) (scalarKoszulFirstMap M rs m) at hm
  rw [((mappingCone.inr f).f i).hom.map_smul] at hm
  exact hm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.LowestTerm
