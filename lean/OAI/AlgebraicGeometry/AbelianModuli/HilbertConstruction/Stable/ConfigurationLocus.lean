import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankKernelClassifier
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Proper
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalFamily

/-! # Configuration Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationLocus

noncomputable section

/-! Pulling the bounded Hilbert parameter back along the actual
configuration kernel classifier imposes the Hilbert conditions on
the stable rank chart. The resulting scheme carries the pulled-back
universal projective family. Additional group and polarization
conditions are still needed for the moduli problem. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (P : Polynomial ℚ)

abbrev configurationHilbertRank : ℕ := (P.eval (D : ℚ)).num.toNat

def stableConfigurationHilbertLocus : Over (Spec (.of R)) :=
  Closed.ParameterIntersections.closedParameterIntersection
    (Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (configurationHilbertRank D P))
    (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ULift.{u} (Fin (configurationHilbertRank D P))) n D
      (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P))

def stableConfigurationHilbertRankInclusion :
    stableConfigurationHilbertLocus R i j D P ⟶
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (configurationHilbertRank D P) :=
  Closed.ParameterIntersections.closedParameterIntersectionFst _ _

def stableConfigurationHilbertParameterMap :
    stableConfigurationHilbertLocus R i j D P ⟶
      HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ULift.{u} (Fin (configurationHilbertRank D P))) n D
        (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) :=
  Closed.ParameterIntersections.closedParameterIntersectionSnd _ _

theorem stableConfigurationHilbert_parameter_condition :
    stableConfigurationHilbertRankInclusion R i j D P ≫
        Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (configurationHilbertRank D P) =
      stableConfigurationHilbertParameterMap R i j D P ≫
        HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) :=
  Closed.ParameterIntersections.closedParameterIntersection_condition _ _

local instance configurationHilbertParameterImmersion :
    IsImmersion (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ULift.{u} (Fin (configurationHilbertRank D P)))
      n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)).left :=
  inferInstanceAs (IsImmersion (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameter (ι := ULift.{u} (Fin (configurationHilbertRank D P)))
    n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)))
local instance configurationHilbertParameterQuasiCompact :
    QuasiCompact (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ULift.{u} (Fin (configurationHilbertRank D P)))
      n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)).left :=
  inferInstanceAs (QuasiCompact (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameter (ι := ULift.{u} (Fin (configurationHilbertRank D P)))
    n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)))

instance stableConfigurationHilbertRankInclusion_isImmersion :
    IsImmersion (stableConfigurationHilbertRankInclusion R i j D P).left :=
  inferInstanceAs (IsImmersion (CategoryTheory.Limits.pullback.fst
    (Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (configurationHilbertRank D P)).left
    (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ULift.{u} (Fin (configurationHilbertRank D P))) n D
      (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)).left))

instance stableConfigurationHilbertRankInclusion_quasiCompact :
    QuasiCompact (stableConfigurationHilbertRankInclusion R i j D P).left :=
  inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.fst
    (Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (configurationHilbertRank D P)).left
    (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ULift.{u} (Fin (configurationHilbertRank D P))) n D
      (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)).left))

def stableConfigurationHilbertPointEquiv (T : Over (Spec (.of R))) :
    (T ⟶ stableConfigurationHilbertLocus R i j D P) ≃
      {p : (T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (configurationHilbertRank D P)) ×
        (T ⟶ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ULift.{u} (Fin (configurationHilbertRank D P))) n D
          (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)) //
        p.1 ≫ Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (configurationHilbertRank D P) =
          p.2 ≫ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)} :=
  Closed.ParameterIntersections.closedParameterIntersectionPointEquiv _ _ T

variable [IsNoetherianRing R]

theorem stableConfigurationHilbertRankInclusion_isClosedImmersion
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (hD : HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ D) :
    IsClosedImmersion (stableConfigurationHilbertRankInclusion R i j D P).left := by
  have : IsClosedImmersion
      (HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ULift.{u} (Fin (configurationHilbertRank D P))) n D
        (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)).left :=
    HilbertScheme.Presentations.BoundedHilbert.Proper.GradedHilbert.boundedHilbertParameter_isClosedImmersion P hP hD (by simp)
  exact Closed.ParameterIntersections.closedParameterIntersectionFst_closed _ _

def stableConfigurationHilbertUniversalFamily :
    HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) (stableConfigurationHilbertLocus R i j D P) :=
  HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (stableConfigurationHilbertParameterMap R i j D P)
    (HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationLocus
