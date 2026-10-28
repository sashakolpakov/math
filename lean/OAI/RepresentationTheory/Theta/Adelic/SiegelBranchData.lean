import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Siegel Branch Data -/

namespace OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

noncomputable section

/-! The branch along the ball determines the branch on the whole Siegel
domain. Existence, uniqueness, and the group law are conclusions. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : BallGeometryData.BallArithmeticData F d m H K}
variable (B : DataTheta.ComparisonData F H K A)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

/-- A full Siegel-domain branch extending the independently defined
Gaussian-operator branch. Its restriction, determinant square, continuity,
holomorphicity, uniqueness, and group law are asserted, not built into a
definition by the desired transformation identity. -/
def SiegelBranchExtension : Prop :=
  ∃ J : RationalSU.ArchimedeanSU F H → Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ → ℂ,
    (∀ g, DifferentiableOn ℂ (J g) Definitions.siegelDomain) ∧
    ContinuousOn (fun p => J p.1 p.2)
      ((Set.univ : Set (RationalSU.ArchimedeanSU F H)) ×ˢ Definitions.siegelDomain) ∧
    (∀ g (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)),
      J g Z.matrix ≠ 0 ∧ J g Z.matrix ^ 2 =
        ((B.symplectic g).complexify.denominator Z.matrix).det) ∧
    (∀ g z, J g (B.period z).matrix = DataTheta.oscillatorFactor B P hd C D g z) ∧
    (∀ g h (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A)),
      J (g * h) Z.matrix = J g ((B.symplectic h).transformSiegel Z).matrix * J h Z.matrix) ∧
    (∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A), J 1 Z.matrix = 1) ∧
    ∀ (g : RationalSU.ArchimedeanSU F H) (j : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ → ℂ),
      ContinuousOn j Definitions.siegelDomain →
      (∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A),
        j Z.matrix ^ 2 = ((B.symplectic g).complexify.denominator Z.matrix).det) →
      (∃ z, j (B.period z).matrix = DataTheta.oscillatorFactor B P hd C D g z) →
      ∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A), j Z.matrix = J g Z.matrix

/-- Any continuous circle-valued lift of the same local SU action equals
the normalized lift. Thus the geometric identification has no residual
continuous-character ambiguity, including at compact real places. -/
def ArchimedeanLiftUniqueness : Prop :=
  ∀ (v : NumberField.InfinitePlace F)
    (s : SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v)) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v)),
    (∀ g, Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (3 * m) C.ψ (.inl v) (s g) =
      Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl v) (FiniteSchwartz.localSUToPair F H K (.inl v) g)) →
    ∀ g, s g = FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g

end

end OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
