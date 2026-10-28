import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralMarkingFamily
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralFiberFactor
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPullbackExt
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.MultiplicationDualFactor
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseTrace

/-! # Central Universal Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The central universal PEL isogeny and its actual dual are
multiplication by q after the constructed marking-family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem CentralUniversalMultiplication.pullback_map_multiplication {S T : Scheme} (b : T ⟶ S)
    (A : Over S) [MonObj A] (n : ℕ) :
    (Over.pullback b).map ((𝟙 A) ^ n) = (𝟙 ((Over.pullback b).obj A)) ^ n :=
  (PELBaseChange.pullback_map_pow b (𝟙 A) n).trans
    (congrArg (fun f => f ^ n) ((Over.pullback b).map_id A))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

include hg hdegree hs hgeometry hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralUniversal_hom_factor
    (j : PELModuli.PELFamilyIso ((D.sourceFamily (Local.IntegralType.central s)).shiftMarking
      (ZMod.unitOfCoprime q hg.2.2.1)) (D.targetFamily (Local.IntegralType.central s))) :
    (D.c46Isogeny hIsogenyQuotient (Local.IntegralType.central s)).isogeny.hom =
      ((𝟙 (D.sourceFamily (Local.IntegralType.central s)).abelian.scheme) ^ q) ≫ j.abelian.hom := by
  have := D.genericSpace_smooth hgeometry
  have : Smooth (D.correspondence (Local.IntegralType.central s)).cover.hom := by
    rw [← (D.correspondence (Local.IntegralType.central s)).source.w]
    infer_instance
  have : IsReduced (D.sourceFamily (Local.IntegralType.central s)).abelian.scheme.left :=
    Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced
      ((D.sourceFamily (Local.IntegralType.central s)).abelian.scheme.hom ≫
        (D.correspondence (Local.IntegralType.central s)).cover.hom)
  apply GeometricPullbackExt.over_hom_ext_geometric_pullback
  intro k _ _ c
  let b := c ≫ (D.correspondence (Local.IntegralType.central s)).cover.hom
  have := FiberLattices.charZero_of_field_spec_map b
  let z : Over.mk b ⟶ (D.correspondence (Local.IntegralType.central s)).cover := Over.homMk c rfl
  have h := D.centralUniversal_fiber_factor hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors b z j
  rw [(Over.pullback c).map_comp, CentralUniversalMultiplication.pullback_map_multiplication]
  exact h

include hdegree hs hgeometry hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralIsMultiplicationByQ : D.CentralIsMultiplicationByQ hIsogenyQuotient hg.2.2.1 := by
  let j := D.centralMarkingFamilyIso hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors
  have hh := D.centralUniversal_hom_factor hg hdegree hs hgeometry hIsogenyQuotient hElementaryDivisors j
  refine ⟨j, hh, ?_⟩
  exact PELIsogenies.PELIsogeny.dual_eq_of_multiplication_factor (ZMod.unitOfCoprime q hg.2.2.1) q
    (D.c46Isogeny hIsogenyQuotient (Local.IntegralType.central s)) j hh

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
