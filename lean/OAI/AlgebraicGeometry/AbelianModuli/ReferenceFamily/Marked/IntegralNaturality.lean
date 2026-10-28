import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DivisionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Integral Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.IntegralNaturality

noncomputable section

/-! The marked integral lattice map of an original algebraic group
morphism is determined by its proved rational-period map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem nativeIntegralMarking_natural_of_periods
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hf : Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A PA).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B PB).inv) =
      (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap)
    (v : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    (Intrinsic.MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking B PB σ s hs hg hdegree (Intrinsic.DivisionNaturality.originalLatticeMap A B PA PB f v)).val =
      u (Intrinsic.MarkedLatticeIso.IntrinsicPELMarking.nativeIntegralMarking A PA ρ s hs hg hdegree v).val := by
  let vQ : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) := ⟨v.val, Submodule.subset_span v.property⟩
  have h := congrArg (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree) (LinearMap.congr_fun hf vQ)
  exact h.trans (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates A B PA PB ρ σ s hs hg hdegree u vQ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.IntegralNaturality
