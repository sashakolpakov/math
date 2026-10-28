import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeEndPoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IdentityCorrespondence

/-! # Integral Hecke Unit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The unit raw correspondence induces the identity of the actual
integral Albanese endomorphism ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

include hg hdegree hs hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.heckeEnd_identity : D.heckeEnd hgeometry (Local.IntegralType.identity s) = 1 := by
  apply D.end_eq_of_component_differences hgeometry
  intro k _ _ b j x y
  rw [D.endPoint_one]
  have h := D.heckeEnd_differences hgeometry (Local.IntegralType.identity s) j x y
  rw [D.albaneseTrace_identity hg hdegree hs hgeometry hIsogenyQuotient] at h
  simpa only [Data.SphericalPELAlbaneseData.endPoint, Data.SphericalPELAlbaneseData.aPoint, Data.SphericalPELAlbaneseData.aTotalPoint, ofMul_div, toMul_sub,
    toMul_ofMul, Category.assoc] using congrArg Additive.ofMul h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
