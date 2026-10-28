import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertPositivity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertTwist
import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertMonotonicity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedSectionGeneration
import OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleProjection

/-! # Closed Hilbert Numerics -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics

noncomputable section

/-! Canonical Hilbert polynomials on actual closed projective schemes,
defined through their coherent direct images. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

def coherentClosedDirectImage (M : X.Modules) := (Scheme.Modules.pushforward f).obj M

instance coherentClosedDirectImage_quasicoherent (M : X.Modules) [M.IsQuasicoherent] :
    (coherentClosedDirectImage f M).IsQuasicoherent :=
  SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f

instance coherentClosedDirectImage_finiteType (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (coherentClosedDirectImage f M).IsFiniteType :=
  SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f

def closedProjectiveTwist (M : X.Modules) (j : Fin (r + 1)) (n : ℕ) : X.Modules :=
  M ⊗ (Scheme.Modules.pullback f).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n)

instance closedProjectiveTwist_quasicoherent (M : X.Modules) [M.IsQuasicoherent]
    (j : Fin (r + 1)) (n : ℕ) : (closedProjectiveTwist f M j n).IsQuasicoherent :=
  (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible
    ((Frame.SectionDetection.Construction.coordinatePositiveTwist_hasFrameSections (R := K) j n).lineBundle.pullback f)).tensorObj_isQuasicoherent

instance closedProjectiveTwist_finiteType (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (r + 1)) (n : ℕ) : (closedProjectiveTwist f M j n).IsFiniteType :=
  (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible
    ((Frame.SectionDetection.Construction.coordinatePositiveTwist_hasFrameSections (R := K) j n).lineBundle.pullback f)).tensorObj_isFiniteType

def closedProjectiveHilbertPolynomial (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (r + 1)) : Polynomial ℚ :=
  Projective.Numerics.Construction.projectiveHilbertPolynomial (coherentClosedDirectImage f M) j

theorem closedProjectiveHilbertPolynomial_iso {M N : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
    (e : M ≅ N) (j : Fin (r + 1)) :
    closedProjectiveHilbertPolynomial f M j = closedProjectiveHilbertPolynomial f N j :=
  Projective.Numerics.Construction.projectiveHilbertPolynomial_iso (coherentClosedDirectImage f M) j
    ((Scheme.Modules.pushforward f).mapIso e)

theorem closedProjectiveHilbertPolynomial_twist (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (r + 1)) (n : ℕ) :
    closedProjectiveHilbertPolynomial f (closedProjectiveTwist f M j n) j =
      Polynomial.taylor (n : ℚ) (closedProjectiveHilbertPolynomial f M j) := by
  let P := (Frame.SectionDetection.Construction.coordinatePositiveTwist_hasFrameSections (R := K) j n).lineBundle
  let e : HilbertTwist.Construction.projectiveTwist (coherentClosedDirectImage f M) j n ≅
      coherentClosedDirectImage f (closedProjectiveTwist f M j n) :=
    LineBundleProjection.Construction.lineBundleProjectionIso f P M
  change Projective.Numerics.Construction.projectiveHilbertPolynomial (coherentClosedDirectImage f (closedProjectiveTwist f M j n)) j = _
  rw [← Projective.Numerics.Construction.projectiveHilbertPolynomial_iso _ j e, HilbertTwist.Construction.projectiveHilbertPolynomial_twist]
  rfl

theorem closedProjectiveHilbertPolynomial_eventually_le_of_mono {M N : X.Modules}
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
    (a : M ⟶ N) [Mono a] (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (closedProjectiveHilbertPolynomial f M j).eval (n : ℚ) ≤
        (closedProjectiveHilbertPolynomial f N j).eval (n : ℚ) :=
  HilbertMonotonicity.Construction.projectiveHilbertPolynomial_eventually_le_of_mono
    (M := coherentClosedDirectImage f M) (N := coherentClosedDirectImage f N)
    ((Scheme.Modules.pushforward f).map a) j

theorem closedProjectiveHilbertPolynomial_leadingCoeff_pos
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (r + 1)) (hM : ¬ IsZero M) :
    0 < (closedProjectiveHilbertPolynomial f M j).leadingCoeff := by
  apply HilbertPositivity.Construction.projectiveHilbertPolynomial_leadingCoeff_pos
  intro hz
  apply hM
  apply (IsZero.iff_id_eq_zero M).mpr
  apply ClosedSectionGeneration.Construction.modulePushforward_map_injective_of_isInducing f f.isClosedEmbedding.isEmbedding.isInducing
  rw [(Scheme.Modules.pushforward f).map_id, (Scheme.Modules.pushforward f).map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hz

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics
