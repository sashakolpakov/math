import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedBlockBasis
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoices

/-! # Polarized Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedChoices.Construction

noncomputable section

/-!
Geometric supported subgroup choices on an actual polarized complex PEL
family are raw rank-three cosets. Both the completion and the integral
block basis are constructed from the given source data. The membership
formula retains the original geometric subgroup.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  {N : ℕ} (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N Foundations.Scheme.ProjectiveSpace.complexBase)
  {δ : Fin (3 * s) → ℕ} {c : NumberField.RingOfIntegers E →+* NumberField.RingOfIntegers E}
  (hF : F.IsPEL δ c) (n : ℕ) (τ : Gal(E/ℚ))
  (M : Type) [AddCommGroup M] [Module (ZMod (q ^ n)) M] [Finite M]
  (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ n) (hdominant : Antitone a)
  (eM : M ≃+ (∀ i, ZMod (q ^ a i)))

def polarizedSupportedRawChoices :
    SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ))
        (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) ≃
      Hecke.Construction.rawRightCosetSupport (BlockLatticeCosets.Construction.blockIntegralLevel q) (BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) :=
  CM.PointsChoices.Construction.l45SupportedRawChoices j iota hsplit (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) F n τ ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    M a ha hdominant (PolarizedBlockBasis.Construction.polarizedCMPointsBlockBasis j iota hsplit s hs hdegree F hF τ) eM

theorem polarizedSupportedRawChoices_membership
    (H : SubgroupFunctor.Construction.SupportedChoice F.abelian.scheme (q ^ n) M
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n τ))
        (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
    (x : CM.PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F τ) :
    (CM.PointsTateBlocks.Construction.l45EvaluateBlock j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F n τ x).val.val.toMul ∈
        H.val.subgroup.points (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (𝟙 _) ↔
      (TateChoices.Construction.standardBoundedLatticeResidues q n).symm
          (Basis.Construction.basisCoordinateResidues q
            (PolarizedBlockBasis.Construction.polarizedCMPointsBlockBasis j iota hsplit s hs hdegree F hF τ) (fun _ => n) x) ∈
        (BlockHeckeChoices.Construction.rawBlockSubgroupChoicesEquiv q n a ha hdominant ElementaryDivisors.Construction.verified_ElementaryDivisorsInput
          (polarizedSupportedRawChoices j iota hsplit s hs hdegree F hF n τ M a ha hdominant eM H)).val :=
  CM.PointsChoices.Construction.l45SupportedRawChoices_membership j iota hsplit (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) F n τ ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    M a ha hdominant (PolarizedBlockBasis.Construction.polarizedCMPointsBlockBasis j iota hsplit s hs hdegree F hF τ) eM H x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedChoices.Construction
