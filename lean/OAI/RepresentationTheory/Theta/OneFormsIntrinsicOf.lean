import OAI.RepresentationTheory.Theta.Adelic.Data
import OAI.RepresentationTheory.Theta.IntrinsicHolomorphic
import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice

/-! # One Forms Intrinsic Of -/

namespace OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic

noncomputable section

/-!
# ThetaOneForms for the complete native AdelicTheta construction

The sole conditional mathematical input is the FULL repaired AdelicTheta proposition.
The final AdelicTheta statement theorem is not imported or invoked. All comparison
maps and their identifications are obtained from its existential conclusion.

For one multiplicity line, `thetaOneForm` is the literal first completed
Taylor tensor in the natural half-determinant/Hodge frame, evaluated in the
two distinguished annihilator slots. Holomorphy, cotangent covariance,
projection surjectivity, finite-Schwartz sparse inputs, and common principal
levels are proved in the owned helpers. No independent period/action/
cofinality/projection/spanning interface is assumed.

The analytic DerivativeFactorization and GaussianConvergence steps use already proved Gaussian derivative
lemmas. CotangentBundle's cotangent identification is realized by the explicit
projective differential calculation. The historical abstract ThetaOneForms theorem
and its statement are unchanged.
-/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicSparse OAI.RepresentationTheory.Theta.IntrinsicHolomorphic.OneFormsIntrinsic
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicDescent

section Conclusion
variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}

/-- Native ThetaOneForms: ordinary holomorphic one-forms, rational covariance, full
spanning before and after projection, and cofinal principal descent with
pointwise spanning at a common level. This is a conclusion, not input data. -/
def NativeConclusion (B : Adelic.DataTheta.ComparisonData F H K A)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P) : Prop :=
  (∀ f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1), Adelic.BallGeometryData.BallHolomorphic (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f)) ∧
  (∀ (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) (u : Fin 2 → ℂ),
    OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f)
        (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val u) =
      OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z u) ∧
  (∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A),
    Submodule.span ℂ (Set.range (fun f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1) =>
      fderiv ℂ (Adelic.DataTheta.completedTheta B f Z.matrix) 0)) = ⊤) ∧
  (∀ z : Adelic.BallNatural.Ball, Submodule.span ℂ (Set.range (fun f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1) =>
    OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z)) = ⊤) ∧
  (∀ (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1))) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
      (N₀ : ℕ), 0 < N₀ →
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧
        ∀ f ∈ Φ, ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ z : Adelic.BallNatural.Ball, ∀ u : Fin 2 → ℂ,
          OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
              (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val u) =
            OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z u) ∧
  (∀ (z : Adelic.BallNatural.Ball) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H)) (N₀ : ℕ), 0 < N₀ →
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        Submodule.span ℂ {ω : OneFormsIntrinsicLattice.IntrinsicProjection.Cotangent | ∃ f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1),
          (∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧ ω = OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z} = ⊤)

end Conclusion

/-- The full native ThetaOneForms theorem. Every geometric/oscillator/theta
identification in the AdelicTheta conclusion is retained for the same witnesses. -/
theorem theta_one_forms_of_complete_AdelicTheta
    (h_AdelicTheta : Adelic.Data.CompleteStatement)
    (F : Type) [Field F] [NumberField F] (d : F) (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K)
    (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) :
    ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1, C.ψ = ψ ∧ Adelic.Data.CharacterConclusion F d 3 1 C ∧
      ∃ D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hq.1 C P,
        Adelic.Data.AdelicConclusion F d 3 1 H K hq.1 C P D ∧
        Adelic.Data.FiniteConclusion F d 3 1 H K hq.1 C P D ∧
        ∃ B : Adelic.DataTheta.ComparisonData F H K A,
          Adelic.DataTheta.CoordinateIdentification B P ∧ Adelic.DataTheta.GeometryIdentification B ∧
          Adelic.DataTheta.OscillatorIdentification B P hq.1 C D ∧ Adelic.SiegelBranchData.SiegelBranchExtension B P hq.1 C D ∧
          Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hq.1 C D ∧ Adelic.DataTheta.Descent.ThetaConstruction B ∧
          Adelic.DataTheta.Descent.RationalHeckeCovariance B P hq.1 C D ∧ Adelic.DataTheta.Descent.CongruenceDescent B P hq.1 C D ∧
          NativeConclusion B P hq.1 C D := by
  obtain ⟨C, hψ, hChar, D, hAd, hFin, B, hCoord, hGeom, hOsc, hBranch,
      hUnique, hTheta, hCov, hDesc⟩ :=
    h_AdelicTheta.2.2 F d hq 1 (Or.inl rfl) H K hH hK ψ hc hu hn hp P A hArch
  refine ⟨C, hψ, hChar, D, hAd, hFin, B, hCoord, hGeom, hOsc, hBranch,
    hUnique, hTheta, hCov, hDesc, ?_⟩
  exact ⟨IntrinsicHolomorphic.OneFormsIntrinsic.thetaOneForm_holomorphic B hGeom hTheta,
    OneFormsIntrinsicLattice.IntrinsicCovariance.thetaOneForm_covariance B P hq.1 C D hGeom hCov,
    OneFormsIntrinsicLattice.IntrinsicSparse.completed_first_span B hTheta, OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm_span B hGeom hTheta,
    OneFormsIntrinsicLattice.IntrinsicDescent.thetaOneForm_principal_descent B P hq.1 C D hGeom hCov hDesc,
    OneFormsIntrinsicLattice.IntrinsicDescent.thetaOneForm_principal_spanning B P hq.1 C D hGeom hTheta hDesc⟩

end

end OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic
