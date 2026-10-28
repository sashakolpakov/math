import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PreconnectedHeckeDifferences
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralAlbaneseTrace
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MarkingFiniteOrder

/-! # Integral Central Unit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The central Hecke endomorphism has finite order on the Albanese,
as follows from the actual marking action and component generation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

local instance Data.SphericalPELAlbaneseData.IntegralCentralUnit_local1 : GrpObj D.albaneseGroup.X := D.albaneseGroup.grp
local instance Data.SphericalPELAlbaneseData.IntegralCentralUnit_local2 : IsCommMonObj D.albaneseGroup.X := D.albaneseGroup.comm

include hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralHeckeEnd_pow_differences (n : ℕ)
    {Y T : Over (Spec (.of K))} [PreconnectedSpace Y.left]
    (i : Y ⟶ D.space) (x y : T ⟶ Y) :
    ((x ≫ i ≫ D.albaneseMap hgeometry) / (y ≫ i ≫ D.albaneseMap hgeometry)) ≫
      TateComparison.End.endSchemeMap D.albaneseGroup.X (D.heckeEnd hgeometry (Local.IntegralType.central s) ^ n) =
        (x ≫ i ≫ ((End.of (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom) ^ n) ≫ D.albaneseMap hgeometry) /
        (y ≫ i ≫ ((End.of (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom) ^ n) ≫ D.albaneseMap hgeometry) := by
  induction n with
  | zero =>
    rw [pow_zero, BaseChange.endSchemeMap_one]
    simp only [pow_zero, Category.comp_id, End.one_def, Category.id_comp]
  | succ n ih =>
    rw [pow_succ', BaseChange.endSchemeMap_mul, ← Category.assoc, ih]
    have h := D.heckeEnd_preconnected_differences hgeometry (Local.IntegralType.central s)
      (i ≫ (End.of (D.qMarkingAutomorphism hgeometry hg.2.2.1).hom) ^ n) x y
    rw [D.albaneseTrace_central hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors] at h
    simpa only [pow_succ', End.mul_def, Category.assoc] using h

include hg hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralHeckeEnd_finiteOrder :
    ∃ n : ℕ, 0 < n ∧ D.heckeEnd hgeometry (Local.IntegralType.central s) ^ n = 1 := by
  obtain ⟨n, hn, hσ⟩ := D.qMarkingAutomorphism_finiteOrder hgeometry hg.2.2.1
  refine ⟨n, hn, ?_⟩
  apply D.end_eq_of_component_differences hgeometry
  intro k _ _ b j x y
  have : PreconnectedSpace (D.componentGeneric j).left := D.genericComponent_preconnected hgeometry j
  rw [D.endPoint_one]
  have h := D.centralHeckeEnd_pow_differences hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors n
    (D.componentInclusion j) x y
  rw [hσ] at h
  simpa only [Data.SphericalPELAlbaneseData.endPoint, Data.SphericalPELAlbaneseData.aPoint, Data.SphericalPELAlbaneseData.aTotalPoint, ofMul_div, toMul_sub, toMul_ofMul,
    End.one_def, Category.id_comp, Category.assoc] using congrArg Additive.ofMul h

include hg hdegree hs hIsogenyQuotient hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralHeckeEnd_isUnit : IsUnit (D.heckeEnd hgeometry (Local.IntegralType.central s)) := by
  obtain ⟨n, hn, he⟩ := D.centralHeckeEnd_finiteOrder hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
  exact IsUnit.of_pow_eq_one he (Nat.ne_of_gt hn)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
