import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitDescent

/-! # Intrinsic Determinant Factorization -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.IntrinsicDescent

/-! The native total top forms and their finite wedge factors live on
one actual torsion-free principal quotient. The level simultaneously
fixes the original total inputs and all transformed tensor factors. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitDescent.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.IntrinsicTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {hd : d ≠ 0} {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁}
variable {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hd P₁ A)
variable (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hd P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def NativeFactorizationAtLevel (c : ℂˣ) (L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : Prop :=
  ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
    (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear Q₁.comparison Q₂.comparison B) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
    ∃ (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3),
      (∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 g x =
        ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 3 (a j) (fun i => x (Fin.castAdd 3 i)) *
          Adelic.Evaluation.finiteSchwartzFunction F 3 (b j) (fun i => x (Fin.natAdd 3 i))) ∧
      (∀ j u, u ∈ L → Adelic.FiniteSchwartz.finiteAction F H K₁ hd Q₁.characters P₁ Q₁.splittings u (a j) = a j) ∧
      (∀ j u, u ∈ L → Adelic.FiniteSchwartz.finiteAction F H S.form hd Q₂.characters P₂ Q₂.splittings u (b j) = b j) ∧
      ∀ z, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z =
        ∑ j, (c : ℂ) • IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a j) z) (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b j) z)

theorem native_common_factorization_descent (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₁ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ) (h₂ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd C (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG : Adelic.DataTheta.GeometryIdentification B) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (hCov : Adelic.DataTheta.Descent.RationalHeckeCovariance B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) hd C D)
    (hDesc : Adelic.DataTheta.Descent.CongruenceDescent B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) hd C D) :
    ∃ c : ℂˣ, ∀ (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F 6)) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
      (N₀ : ℕ), 0 < N₀ →
      ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
          (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
          (∀ f ∈ Φ, ∀ g ∈ L,
            Adelic.FiniteSchwartz.finiteAction F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd C (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) D g f = f) ∧
          ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w),
            CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧ SecondCountableTopology (Quotient R) ∧
            ∀ f ∈ Φ, NativeFactorizationAtLevel Q₁ Q₂ B c L f ∧ Adelic.BallGeometryData.BallSmooth (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f) ∧
              ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
                Continuous descended ∧ (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
                ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z) := by
  have hvalid₁ := h₁
  have hvalid₂ := h₂
  obtain ⟨_,_,_,_,hC₁,hG₁,_,_,_,hΘ₁,_,_,_⟩ := hvalid₁
  obtain ⟨_,_,_,_,hC₂,hG₂,_,_,_,hΘ₂,_,_,_⟩ := hvalid₂
  let c : ℂˣ := Units.mk0 (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio Q₁.comparison Q₂.comparison B IntrinsicBallTopology.Intrinsic.origin)⁻¹
    (inv_ne_zero (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_nonzero Q₁.comparison Q₂.comparison B hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin))
  choose g hg using fun f : Adelic.FiniteSchwartz.finiteSchwartz F 6 =>
    IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear Q₁.comparison Q₂.comparison B)
  refine ⟨c,?_⟩
  intro Φ K₀ N₀ hN₀
  let Ψ := Φ ∪ Φ.image g
  obtain ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,hforms⟩ :=
    IntrinsicSplitDescent.Intrinsic.common_native_descent Q₁ Q₂ B ψ h₁ h₂ hE₁ hE₂ hTensorDecomposition (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) C D hG hDesc Ψ K₀ N₀ hN₀
  have hΦ (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (hf : f ∈ Φ) : f ∈ Ψ := Finset.mem_union_left _ hf
  have hΦg (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (hf : f ∈ Φ) : g f ∈ Ψ :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  refine ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,(fun f hf => hfix f (hΦ f hf)),R,hR,hRc,hRt,hRs,?_⟩
  intro f hf
  obtain ⟨⟨n,a,b,he,ha,hb,hw⟩,_,_⟩ := hforms (g f) (hΦg f hf)
  refine ⟨⟨g f,hg f,n,a,b,he,ha,hb,?_⟩,IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth B hΘ f,?_⟩
  · intro z
    rw [IntrinsicFixedFactorization.Intrinsic.native_top_comparison Q₁.comparison Q₂.comparison B hC₁ hC₂ hC hG₁ hG₂ hG
      hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hΘ f (g f) (hg f) z,hw,Finset.smul_sum]
    rfl
  · apply IntrinsicSplitDescent.Intrinsic.smooth_top_section B N R hR _ (IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth B hΘ f)
    intro u hu z
    have h := IntrinsicSecondAction.Intrinsic.thetaTopForm_covariance B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) hd C D hG hCov u f z
    rw [hfix f (hΦ f hf) _ (hcontain u hu)] at h
    exact h

end RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.IntrinsicDescent

namespace RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.Intrinsic

/-! The native determinant constant and finite wedge factors on one
actual torsion-free principal quotient. The constant is the inverse
half-frame ratio, and its square is the fixed coordinate determinant. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitDescent.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.IntrinsicTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {hd : d ≠ 0} {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁}
variable {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hd P₁ A)
variable (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hd P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.IntrinsicDescent

theorem native_determinant_factorization_descent (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₁ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ) (h₂ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd C (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG : Adelic.DataTheta.GeometryIdentification B) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (hCov : Adelic.DataTheta.Descent.RationalHeckeCovariance B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) hd C D)
    (hDesc : Adelic.DataTheta.Descent.CongruenceDescent B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) hd C D) :
    ∃ c : ℂˣ,
      (c : ℂ) = (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio Q₁.comparison Q₂.comparison B IntrinsicBallTopology.Intrinsic.origin)⁻¹ ∧
      (c : ℂ) ^ 2 = LinearMap.det (IntrinsicDeterminantComparison.Intrinsic.frameComparison Q₁.comparison Q₂.comparison B) ∧
      (∀ z, B.halfFrame z * (c : ℂ) = Q₁.comparison.halfFrame z * Q₂.comparison.halfFrame z) ∧
      ∀ (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F 6)) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
      (N₀ : ℕ), 0 < N₀ →
      ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
          (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
          (∀ f ∈ Φ, ∀ g ∈ L,
            Adelic.FiniteSchwartz.finiteAction F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd C (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) D g f = f) ∧
          ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w),
            CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧ SecondCountableTopology (Quotient R) ∧
            ∀ f ∈ Φ, IntrinsicDescent.NativeFactorizationAtLevel Q₁ Q₂ B c L f ∧ Adelic.BallGeometryData.BallSmooth (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f) ∧
              ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
                Continuous descended ∧ (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
                ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z) := by
  have hvalid₁ := h₁
  have hvalid₂ := h₂
  obtain ⟨_,_,_,_,hC₁,hG₁,_,_,_,hΘ₁,_,_,_⟩ := hvalid₁
  obtain ⟨_,_,_,_,hC₂,hG₂,_,_,_,hΘ₂,_,_,_⟩ := hvalid₂
  let c : ℂˣ := Units.mk0 (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio Q₁.comparison Q₂.comparison B IntrinsicBallTopology.Intrinsic.origin)⁻¹
    (inv_ne_zero (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_nonzero Q₁.comparison Q₂.comparison B hG₁ hG₂ hG IntrinsicBallTopology.Intrinsic.origin))
  choose g hg using fun f : Adelic.FiniteSchwartz.finiteSchwartz F 6 =>
    IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear Q₁.comparison Q₂.comparison B)
  refine ⟨c,rfl,?_,?_,?_⟩
  · change (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio Q₁.comparison Q₂.comparison B IntrinsicBallTopology.Intrinsic.origin)⁻¹ ^ 2 = _
    rw [inv_pow,IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_square Q₁.comparison Q₂.comparison B hC₁ hC₂ hC hG₁ hG₂ hG,inv_inv]
  · intro z
    change B.halfFrame z * (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio Q₁.comparison Q₂.comparison B IntrinsicBallTopology.Intrinsic.origin)⁻¹ = _
    rw [← IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio_constant Q₁.comparison Q₂.comparison B hC₁ hC₂ hC hG₁ hG₂ hG z,
      IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio,inv_div]
    field_simp [(hG.2.2.2.2.2.1 z).1]
  intro Φ K₀ N₀ hN₀
  let Ψ := Φ ∪ Φ.image g
  obtain ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,hforms⟩ :=
    IntrinsicSplitDescent.Intrinsic.common_native_descent Q₁ Q₂ B ψ h₁ h₂ hE₁ hE₂ hTensorDecomposition (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) C D hG hDesc Ψ K₀ N₀ hN₀
  have hΦ (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (hf : f ∈ Φ) : f ∈ Ψ := Finset.mem_union_left _ hf
  have hΦg (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (hf : f ∈ Φ) : g f ∈ Ψ :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  refine ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,(fun f hf => hfix f (hΦ f hf)),R,hR,hRc,hRt,hRs,?_⟩
  intro f hf
  obtain ⟨⟨n,a,b,he,ha,hb,hw⟩,_,_⟩ := hforms (g f) (hΦg f hf)
  refine ⟨⟨g f,hg f,n,a,b,he,ha,hb,?_⟩,IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth B hΘ f,?_⟩
  · intro z
    rw [IntrinsicFixedFactorization.Intrinsic.native_top_comparison Q₁.comparison Q₂.comparison B hC₁ hC₂ hC hG₁ hG₂ hG
      hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hΘ f (g f) (hg f) z,hw,Finset.smul_sum]
    rfl
  · apply IntrinsicSplitDescent.Intrinsic.smooth_top_section B N R hR _ (IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth B hΘ f)
    intro u hu z
    have h := IntrinsicSecondAction.Intrinsic.thetaTopForm_covariance B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) hd C D hG hCov u f z
    rw [hfix f (hΦ f hf) _ (hcontain u hu)] at h
    exact h

end RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.Intrinsic

end

end OAI
