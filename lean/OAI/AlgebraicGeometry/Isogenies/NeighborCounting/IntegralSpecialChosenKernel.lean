import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors

/-! # Integral Special Chosen Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel

noncomputable section

/-! The actual integral quotient's chosen-kernel criteria after arbitrary
base change. The special-fiber compact powers and active subgroup follow
from the original complete quotient and its coefficient projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalQuotientKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors.ChosenKernelCriterion

private theorem mulEquiv_pow_eq_one {V W : Type*} [Group V] [Group W]
    (e : V ≃* W) (x : V) (m : ℕ) : (e x) ^ m = 1 ↔ x ^ m = 1 := by
  constructor
  · intro h
    apply e.injective
    exact (map_pow e x m).trans (h.trans e.map_one.symm)
  · intro h
    exact (map_pow e x m).symm.trans ((congrArg e h).trans e.map_one)

variable {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N s : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hdegree : q.Coprime (∏ i, δ i))
  (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (.inr v) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (.inl v))
  (n : ℕ) (hn : 1 ≤ n) (active : Fin s) (multiplicative : Fin s → Bool)
  (H : Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (ρ.map (j.projector iota hsplit 1 (labels (.inl active))))))

variable {T : Scheme} (b : T ⟶ S)

local notation "G" => Grp.mk A.abelian.scheme
local notation "F" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralCanonicalNeighbors.integralCanonicalFullKernel j iota hsplit A ρ labels n active multiplicative (Over.mk b) H

theorem integralSpecial_kernel_iff (U : Over T) (x : U ⟶ (A.abelian.pullback b).scheme) :
    x ≫ ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom = 1 ↔
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x ∈
        (F).points ((Over.map b).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) U) := by
  change x ∈ (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom).points U (toUnit U) ↔ _
  rw [IntegralCanonicalQuotientKernel.integralCanonicalQuotient_pullback_nativeKernel j iota hsplit A ρ hρ hdegree
    labels hlabels n hn active multiplicative H b]
  exact AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter_membership G (Over.mk b) F U (toUnit U) x

omit [IsReduced S] [IsLocallyNoetherian S] [NumberField.IsCMField E] in
private theorem pulledChosenPoint_fixed (v : Fin s) (U : Over T)
    (x : U ⟶ (A.abelian.pullback b).scheme)
    (hx : x ≫ (Over.pullback b).map (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v) = x) :
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x ≫
      AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v =
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x :=
  (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp b
    (show G ⟶ G from Grp.homMk (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v)) U x).symm.trans
      (congrArg (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm hx)

theorem integralSpecial_active_kernel (U : Over T) (x : U ⟶ (A.abelian.pullback b).scheme)
    (hx : x ≫ (Over.pullback b).map
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels active) = x) :
    x ≫ ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom = 1 ↔
      x ∈ (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G (Over.mk b)
        (IntegralCanonicalNeighbors.integralActiveFamily j iota hsplit A ρ labels active (Over.mk b) H)).points U (toUnit U) := by
  have hf := integralSpecial_kernel_iff j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative H b U x
  have hc := IntegralCanonicalNeighbors.ChosenKernelCriterion.integralCanonicalFullKernel_chosen_component j iota hsplit A ρ labels n hn
    active multiplicative (Over.mk b) H active ((Over.map b).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) U)
    ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x)
    (pulledChosenPoint_fixed j iota hsplit A ρ labels n b active U x hx)
  simp only [Kernel.Base.chosenKernel, ↓reduceIte] at hc
  exact hf.trans hc

theorem integralSpecial_compact_multiplicative
    (v : Fin s) (hv : v ≠ active) (hm : multiplicative v = true)
    (U : Over T) (x : U ⟶ (A.abelian.pullback b).scheme)
    (hx : x ≫ (Over.pullback b).map
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v) = x) :
    x ≫ ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom = 1 ↔ x ^ (q ^ n) = 1 := by
  have hf := integralSpecial_kernel_iff j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative H b U x
  have hc := IntegralCanonicalNeighbors.ChosenKernelCriterion.integralCanonicalFullKernel_compact_multiplicative j iota hsplit A ρ labels n hn
    active multiplicative (Over.mk b) H v hv hm ((Over.map b).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) U)
    ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x)
    (pulledChosenPoint_fixed j iota hsplit A ρ labels n b v U x hx)
  apply (hf.trans hc).trans
  exact mulEquiv_pow_eq_one (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x (q ^ n)

theorem integralSpecial_compact_etale
    (v : Fin s) (hv : v ≠ active) (he : multiplicative v = false)
    (U : Over T) (x : U ⟶ (A.abelian.pullback b).scheme)
    (hx : x ≫ (Over.pullback b).map
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v) = x) :
    x ≫ ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom = 1 ↔ x = 1 := by
  have hf := integralSpecial_kernel_iff j iota hsplit A ρ hρ hdegree labels hlabels
    n hn active multiplicative H b U x
  have hc := IntegralCanonicalNeighbors.ChosenKernelCriterion.integralCanonicalFullKernel_compact_etale j iota hsplit A ρ labels n hn
    active multiplicative (Over.mk b) H v hv he ((Over.map b).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) U)
    ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm x)
    (pulledChosenPoint_fixed j iota hsplit A ρ labels n b v U x hx)
  exact (hf.trans hc).trans (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv b G U).symm.map_eq_one_iff

theorem integralSpecial_compact_iff (v : Fin s) (hv : v ≠ active)
    (U : Over T) (x : U ⟶ (A.abelian.pullback b).scheme)
    (hx : x ≫ (Over.pullback b).map
      (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A.abelian ρ n s labels v) = x) :
    x ≫ ((IntegralCanonicalNeighbors.integralCanonicalQuotient j iota hsplit A ρ hρ hdegree labels hlabels
      n hn active multiplicative (Over.mk (𝟙 S)) H).identitySourceIsogeny.pullback b).hom = 1 ↔
      if multiplicative v then x ^ (q ^ n) = 1 else x = 1 := by
  cases hc : multiplicative v
  · simpa only [hc, Bool.false_eq_true, ↓reduceIte] using
      integralSpecial_compact_etale j iota hsplit A ρ hρ hdegree labels hlabels
        n hn active multiplicative H b v hv hc U x hx
  · simpa only [hc, ↓reduceIte] using
      integralSpecial_compact_multiplicative j iota hsplit A ρ hρ hdegree labels hlabels
        n hn active multiplicative H b v hv hc U x hx

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel
