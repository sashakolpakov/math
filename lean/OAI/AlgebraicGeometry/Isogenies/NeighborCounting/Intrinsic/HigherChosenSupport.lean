import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

/-! # Higher Chosen Support -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport

noncomputable section

/-! An original lower-level chosen subgroup is fixed by every higher
lift of its coefficient projector. The equality follows from the proved
coefficient congruence and the subgroup's literal lower torsion bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChosenFamilyProperties.IntrinsicFamily OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable {m n : ℕ} (hmn : m ≤ n) (τ : Gal(E/ℚ))
variable {H : Grp (Over S)} {P : Over S}
variable (i : H ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ m τ).toGrp)

include hmn in
theorem original_block_family_supported_higher :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (Kernel.Base.fixedKernelFamily (P := P) (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ m τ))
      (σ.map (j.projector iota hsplit n τ)) := by
  have hp := ChosenFamilyProperties.IntrinsicFamily.original_block_family_bound (P := P) j iota hsplit A σ m τ i
  intro T t a ha
  have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ m)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hmn τ)
    T a (hp.1 T t a ha)
  exact hc.trans (hp.2 T t a ha)

include hmn in
theorem original_block_inclusion_supported_higher :
    (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ m τ) ≫
      σ.map (j.projector iota hsplit n τ) =
        i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ m τ :=
  original_block_family_supported_higher j iota hsplit A σ hmn τ i
    H.X (toUnit H.X) _ ⟨𝟙 H.X, by
      change (𝟙 H.X) ≫ (i.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A σ m τ) = _
      exact Category.id_comp _⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport
