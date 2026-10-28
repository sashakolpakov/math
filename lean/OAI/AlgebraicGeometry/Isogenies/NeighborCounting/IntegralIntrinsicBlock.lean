import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockFlatness
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedTorsionFiniteness

/-! # Integral Intrinsic Block -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic

noncomputable section

/-! Finite local freeness of the literal IsogenyQuotient block over the integral
source follows from the source polarization and the original CMPoints
projector retraction. Its rank agrees with that of the CMPoints block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
  (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
  (n : ℕ) (τ : Gal(E/ℚ))

theorem integralCMPointsBlock_finiteLocallyFree :
    IsFinite (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n τ).X.hom ∧
      Flat (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n τ).X.hom ∧
      LocallyOfFinitePresentation (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n τ).X.hom := by
  obtain ⟨hf, hflat, hfp⟩ := PELModuli.CMPoints.PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free PEL (Fact.out : q.Prime).pos n
  let : IsFinite (PEL.abelian.torsionScheme (q ^ n)).hom := hf
  let : Flat (PEL.abelian.torsionScheme (q ^ n)).hom := hflat
  let : LocallyOfFinitePresentation (PEL.abelian.torsionScheme (q ^ n)).hom := hfp
  exact PELModuli.CMPoints.RelativeBlockFlatness.split_block_finite_locally_free j iota hsplit PEL.abelian ρ n τ

theorem integralNativeBlock_finiteLocallyFree :
    IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))).hom ∧
      Flat (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))).hom ∧
      LocallyOfFinitePresentation (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))).hom := by
  obtain ⟨hf, hflat, hfp⟩ := integralCMPointsBlock_finiteLocallyFree j iota hsplit PEL ρ n τ
  let : IsFinite (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme PEL.abelian ρ (q ^ n) (j.projector iota hsplit n τ)).hom := hf
  let : Flat (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme PEL.abelian ρ (q ^ n) (j.projector iota hsplit n τ)).hom := hflat
  let : LocallyOfFinitePresentation
      (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme PEL.abelian ρ (q ^ n) (j.projector iota hsplit n τ)).hom := hfp
  let e := AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit PEL.abelian ρ n τ
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [← e.hom.w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem integralNativeBlock_rank (x : S) :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))).hom.finrank x =
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ n τ).X.hom.finrank x := by
  obtain ⟨hf, hflat, _⟩ := integralCMPointsBlock_finiteLocallyFree j iota hsplit PEL ρ n τ
  let : IsFinite (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme PEL.abelian ρ (q ^ n) (j.projector iota hsplit n τ)).hom := hf
  let : Flat (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme PEL.abelian ρ (q ^ n) (j.projector iota hsplit n τ)).hom := hflat
  let e := AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit PEL.abelian ρ n τ
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [← e.hom.w]
  exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left _) x

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic
