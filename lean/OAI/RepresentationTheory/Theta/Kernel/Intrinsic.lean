import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCore
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedConstruction

/-! # Intrinsic -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.Intrinsic.IntrinsicAssembly

/-! Assembly of the native determinant factorization, exact finite
transport, nonvanishing and the C-infinity family at one common level. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompletionData.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianFixedLevel.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLevelSmoothTop.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.IntrinsicDescent OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantFactorization.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedFactorization.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactTensorMatch.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedConstruction.IntrinsicConstruction OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {hd : d ≠ 0} {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁}
variable {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hd P₁ A)
variable (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hd P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))
variable (Q : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S),
  IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicCompactChoices.Intrinsic.choiceArithmetic (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) p))

theorem assemble_native_conclusion (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK₁ : K₁.val.conjTranspose = -K₁.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ)
    (h₁ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ) (h₂ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ)
    (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hQ : ∀ p, IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ)
    (hFirstGaussian : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hSecondGaussian : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hSumGaussian : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0}) :
    IntrinsicCompletionData.Intrinsic.NativeConclusion Q₁ Q₂ Q₀ Q ψ h₀ hQ hSumGaussian := by
  have hvalid₁ := h₁
  have hvalid₂ := h₂
  have hvalid₀ := h₀
  obtain ⟨_,_,_,_,hC₁,hG₁,_,_,_,hΘ₁,_,_,_⟩ := hvalid₁
  obtain ⟨_,_,_,_,hC₂,hG₂,_,_,_,hΘ₂,_,_,_⟩ := hvalid₂
  obtain ⟨_,_,_,_,hC₀,hG₀,_,_,_,hΘ₀,hCov₀,hDesc₀,_⟩ := hvalid₀
  obtain ⟨c,hc,hc2,hhalf,hlevels⟩ := IntrinsicDeterminantFactorization.Intrinsic.native_determinant_factorization_descent Q₁ Q₂ Q₀.comparison
    ψ h₁ h₂ hFirstGaussian hSecondGaussian hSumGaussian hTensorDecomposition Q₀.characters Q₀.splittings hC₀ hG₀ hΘ₀ hCov₀ hDesc₀
  obtain ⟨_,_,hnonzero⟩ := IntrinsicFixedFactorization.Intrinsic.native_fixed_factorization Q₁.comparison Q₂.comparison Q₀.comparison
    hC₁ hC₂ hC₀ hG₁ hG₂ hG₀ hFirstGaussian hSecondGaussian hSumGaussian hTensorDecomposition hΘ₁ hΘ₂ hΘ₀
  refine ⟨c,hc,hc2,hhalf,hnonzero,?_,?_⟩
  · intro p f
    obtain ⟨_,_,_,_,hCp,hGp,_,_,_,hΘp,_,_,_⟩ := hQ p
    obtain ⟨g,hg⟩ := IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f
      (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p Q₀.comparison (Q p).comparison)
    exact ⟨g,hg,fun a z => IntrinsicCompactTensorMatch.Intrinsic.compact_normalized_tensor_match p Q₀.comparison (Q p).comparison
      hC₀ hCp hG₀ hGp hSumGaussian hΘ₀ hΘp f g hg a z⟩
  · intro Φ K₀ N₀ hN₀
    obtain ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,hforms⟩ := hlevels Φ K₀ N₀ hN₀
    refine ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,?_⟩
    intro f hf
    have hff (g : Adelic.SpecialUnitary.SU H.val) (hg : Adelic.BallGeometryData.PrincipalLevel N g) :
        Adelic.FiniteSchwartz.finiteAction F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd Q₀.characters (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) Q₀.splittings
          (Adelic.RationalSU.rationalFiniteSU F H g) f = f := hfix f hf _ (hcontain g hg)
    have hK := IntrinsicSplitting.IntrinsicArithmetic.blockUnit_skewHermitian S.form hK₁ S.skewHermitian
    let family := IntrinsicLagrangianFixedLevel.Intrinsic.nativeLagrangianAtLevel Q₀ Q ψ h₀ hQ hSumGaussian hns hH hK hArch N f hff
    refine ⟨(hforms f hf).1,family,?_,fun _ => rfl,?_,?_⟩
    · exact IntrinsicLagrangianFixedLevel.Intrinsic.native_lagrangian_at_level_continuous Q₀ Q ψ h₀ hQ hSumGaussian hns hH hK hArch N f hff
    · intro z
      exact IntrinsicLagrangianFixedLevel.Intrinsic.native_lagrangian_base Q₀ Q ψ h₀ hQ hSumGaussian f z
    · intro p
      exact IntrinsicLevelSmoothTop.Intrinsic.level_smooth_top_descends Q₀.comparison N (family p) R hR

end RepresentationTheory.Theta.Kernel.Intrinsic.IntrinsicAssembly

namespace RepresentationTheory.Theta.Kernel.Intrinsic

/-! The two one-form constructions use the supplied cotangent and derivative
prerequisites, and every total and compact witness uses the full adelic theta
input. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction OAI.RepresentationTheory.Theta.Kernel.Intrinsic.IntrinsicAssembly

theorem theta_top_forms : IntrinsicCore.Intrinsic.Statement := by
  intro _hCotangentBundle _hDerivativeFactorization hTensorDecomposition hThetaOneForms hAdelicTheta F _ _ d hq H K₁ hH hK₁ ψ hc hu hn hp A S P₁ P₂ hArch hFirstGaussian hSecondGaussian hSumGaussian
  obtain ⟨C₁,hψ₁,hChar₁,D₁,hAd₁,hFin₁,B₁,hC₁,hG₁,hO₁,hBr₁,hU₁,hΘ₁,hCov₁,hDesc₁,hOne₁⟩ :=
    hThetaOneForms hAdelicTheta F d hq H K₁ hH hK₁ ψ hc hu hn hp P₁ A hArch
  obtain ⟨C₂,hψ₂,hChar₂,D₂,hAd₂,hFin₂,B₂,hC₂,hG₂,hO₂,hBr₂,hU₂,hΘ₂,hCov₂,hDesc₂,hOne₂⟩ :=
    hThetaOneForms hAdelicTheta F d hq H S.form hH S.skewHermitian ψ hc hu hn hp P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) hArch
  let Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hq.1 P₁ A := ⟨C₁,D₁,B₁⟩
  let Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hq.1 P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) := ⟨C₂,D₂,B₂⟩
  have h₁ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ :=
    ⟨hψ₁,hChar₁,hAd₁,hFin₁,hC₁,hG₁,hO₁,hBr₁,hU₁,hΘ₁,hCov₁,hDesc₁,hOne₁⟩
  have h₂ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ :=
    ⟨hψ₂,hChar₂,hAd₂,hFin₂,hC₂,hG₂,hO₂,hBr₂,hU₂,hΘ₂,hCov₂,hDesc₂,hOne₂⟩
  have hK := IntrinsicSplitting.IntrinsicArithmetic.blockUnit_skewHermitian S.form hK₁ S.skewHermitian
  obtain ⟨C,hψ,hChar,D,hAd,hFin,B,hCoord,hGeom,hOsc,hBranch,hUnique,hTheta,hCov,hDesc,_,_,hTop⟩ :=
    IntrinsicCompactChoices.IntrinsicSecondConstruction.construct_total hAdelicTheta hq hH hK ψ hc hu hn hp (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) hArch
  let Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hq.1 (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) := ⟨C,D,B⟩
  have h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ :=
    ⟨hψ,hChar,hAd,hFin,hCoord,hGeom,hOsc,hBranch,hUnique,hTheta,hCov,hDesc,hTop⟩
  obtain ⟨Q,hQ⟩ := IntrinsicCompactChoices.Intrinsic.construct_compact_choices hAdelicTheta hq hH hK ψ hc hu hn hp
    (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) hArch
  exact ⟨Q₁,Q₂,Q₀,Q,h₁,h₂,h₀,hQ,
    IntrinsicAssembly.assemble_native_conclusion Q₁ Q₂ Q₀ Q hq.2 hH hK₁ ψ hArch h₁ h₂ h₀ hQ hFirstGaussian hSecondGaussian hSumGaussian hTensorDecomposition⟩

end RepresentationTheory.Theta.Kernel.Intrinsic

end

end OAI
