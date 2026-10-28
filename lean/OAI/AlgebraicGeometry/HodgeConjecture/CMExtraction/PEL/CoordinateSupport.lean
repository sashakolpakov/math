import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FilledSupport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FinitePELHomeomorph
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates

/-! # Coordinate Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.CoordinateSupport

noncomputable section

/-! The filled PEL operator agrees with the original operator at all
primes other than q in every retained rational basis. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

namespace TestTransport

theorem linearMap_smul_of_matrix_support
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : R) (f g : (I → S) →ₗ[S] (I → S))
    (h : ∀ i j, a • (f (Pi.single j 1) i - g (Pi.single j 1) i) =
      f (Pi.single j 1) i - g (Pi.single j 1) i) (x : I → S) :
    a • (f x - g x) = f x - g x := by
  have he (F : (I → S) →ₗ[S] (I → S)) : F x = ∑ j, x j • F (Pi.single j 1) := by
    simp_rw [← F.map_smul]
    rw [← map_sum]
    congr 1
    funext i
    simp [Pi.single_apply]
  rw [he f, he g, ← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_sub, smul_comm]
  congr 1
  funext i
  exact h i j

end TestTransport

namespace Approximation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hb : IsCMField.complexConj E P.b = P.b) (hb0 : P.b ≠ 0)

theorem cmFinitePEL_matrix_entry
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)) (i j : Fin 3) :
    (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0 g).val (Pi.single j 1) i =
      (CM.FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 P.b hb hb0 g).val.val i j :=
  UnitaryLinear.Approximation.matrixPELUnitary_entry E P _ i j

theorem cmFinitePEL_filled_support
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)) (i j : Fin 3) :
    RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q •
      ((CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0
        (RestrictedInsert.Approximation.restrictedInsertPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) (RestrictedAwaySame.Approximation.restrictedForgetPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) g))).val
          (Pi.single j 1) i -
        (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0 g).val (Pi.single j 1) i) =
      (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0
        (RestrictedInsert.Approximation.restrictedInsertPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) (RestrictedAwaySame.Approximation.restrictedForgetPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) g))).val
          (Pi.single j 1) i -
        (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0 g).val (Pi.single j 1) i := by
  simp only [cmFinitePEL_matrix_entry]
  exact CM.FilledSupport.Approximation.cmFiniteTensor_filled_support E σ δ hδ hδ0 P.b hb hb0 g i j

theorem cmFinitePEL_filled_coordinate_other
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0))
    (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)
    (f : (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) →ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p
      (f ((CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0
        (RestrictedInsert.Approximation.restrictedInsertPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) (RestrictedAwaySame.Approximation.restrictedForgetPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) g))).val x)) =
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p
        (f ((CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0 g).val x)) :=
  RationalPrimeSupport.TestTransport.supported_linear_difference q p hpq f _ _
    (TestTransport.linearMap_smul_of_matrix_support (RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q) _ _
      (cmFinitePEL_filled_support E σ δ hδ hδ0 P hb hb0 g) x)

end Approximation

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.CoordinateSupport
