import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SplitSequence
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! # Split Sequence Cochain -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSequenceCochain

noncomputable section

/-! Cochain formulas for the connecting map of a degreewise split sequence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R]
  (S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)

theorem δ_retraction : δ 0 1 (Tensor.SplitSequence.retraction R S σ) =
    -(Cochain.ofHom S.g).comp (cocycleOfDegreewiseSplit S σ).1 (zero_add 1) := by
  apply Cochain.ext
  intro n m hnm
  rw [δ_zero_cochain_v]
  simp only [Cochain.neg_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Tensor.SplitSequence.retraction, Cochain.ofHoms_v,
    cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v]
  let r (i : ℤ) : S.X₂.X i ⟶ S.X₁.X i := (σ i).r
  let s (i : ℤ) : S.X₃.X i ⟶ S.X₂.X i := (σ i).s
  change r n ≫ S.X₁.d n m - S.X₂.d n m ≫ r m =
    -(S.g.f n ≫ s n ≫ S.X₂.d n m ≫ r m)
  have hfr : S.f.f m ≫ r m = 𝟙 _ := (σ m).f_r
  have hrf : r n ≫ S.f.f n = 𝟙 _ - S.g.f n ≫ s n := (σ n).r_f
  have he : r n ≫ S.X₁.d n m =
      S.X₂.d n m ≫ r m - S.g.f n ≫ s n ≫ S.X₂.d n m ≫ r m := by
    calc
      _ = r n ≫ S.X₁.d n m ≫ S.f.f m ≫ r m := by
        rw [hfr, Category.comp_id]
      _ = (r n ≫ S.f.f n) ≫ S.X₂.d n m ≫ r m := by
        rw [← S.f.comm_assoc n m]
        simp only [Category.assoc]
      _ = _ := by
        rw [hrf]
        simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
  rw [he]
  abel

theorem desc_cochain : Cochain.ofHom (mappingCone.descShortComplex S) =
    (mappingCone.snd S.f).comp (Cochain.ofHom S.g) (zero_add 0) := by
  rw [mappingCone.descShortComplex, mappingCone.ofHom_desc, mappingCone.descCochain,
    Cochain.comp_zero, zero_add]

def comparisonHomotopy : Cochain (mappingCone S.f) S.X₁ 0 :=
  (mappingCone.snd S.f).comp (Tensor.SplitSequence.retraction R S σ) (zero_add 0)

theorem cone_connecting : -(mappingCone.fst S.f).1 =
    (Cochain.ofHom (mappingCone.descShortComplex S)).comp (cocycleOfDegreewiseSplit S σ).1 (zero_add 1) +
      δ 0 1 (comparisonHomotopy R S σ) := by
  have hd : δ 0 1 (comparisonHomotopy R S σ) =
      -(Cochain.ofHom (mappingCone.descShortComplex S)).comp (cocycleOfDegreewiseSplit S σ).1 (zero_add 1) -
        (mappingCone.fst S.f).1 := by
    rw [comparisonHomotopy, δ_comp_zero_cochain _ _ 1 (zero_add 1),
      δ_retraction, mappingCone.δ_snd, Cochain.comp_neg, Cochain.neg_comp,
      Cochain.comp_assoc_of_second_is_zero_cochain, Tensor.SplitSequence.f_retraction, Cochain.comp_id,
      ← Cochain.comp_assoc_of_second_is_zero_cochain, ← desc_cochain]
    rw [sub_eq_add_neg]
  rw [hd]
  abel

theorem tensor_cone_connecting (K : CochainComplex (ModuleCat.{0} R) ℤ) :
    -Tensor.Cochain.map R K (mappingCone.fst S.f).1 =
      (Cochain.ofHom ((Tensor.Homotopy.complexFunctor R K).map (mappingCone.descShortComplex S))).comp
        (Tensor.Cochain.map R K (cocycleOfDegreewiseSplit S σ).1) (zero_add 1) +
      δ 0 1 (Tensor.Cochain.map R K (comparisonHomotopy R S σ)) := by
  have h := congrArg (Tensor.Cochain.map R K) (cone_connecting R S σ)
  simpa only [Tensor.Cochain.map_neg, Tensor.Cochain.map_add, Tensor.Cochain.map_comp,
    Tensor.Cochain.map_ofHom, Tensor.Cochain.map_δ] using h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitSequenceCochain
