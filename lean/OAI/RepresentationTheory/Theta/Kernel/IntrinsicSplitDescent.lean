import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitRegularity
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent

/-! # Intrinsic Split Descent -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitDescent.Intrinsic

noncomputable section

/-! A finite family of the constructed split tensors descends on the
same native principal quotient as the total multiplicity-two family.
The individual factors are fixed at this common level. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitRegularity.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {hd : d ≠ 0} {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁}
variable {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (Q₁ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses K₁ hd P₁ A)
variable (Q₂ : IntrinsicSplitting.IntrinsicSummands.SummandWitnesses S.form hd P₂ (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem total_ball_action (h₁ : Adelic.DataTheta.GeometryIdentification Q₁.comparison)
    (hB : Adelic.DataTheta.GeometryIdentification B) : Q₁.comparison.ball = B.ball := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  exact (h₁.2.1 g).trans (hB.2.1 g).symm

theorem smooth_top_section (N : ℕ) (R : Setoid Adelic.BallNatural.Ball)
    (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w)
    (ω : Adelic.BallNatural.Ball → IntrinsicExterior.Intrinsic.TopCovector) (hω : Adelic.BallGeometryData.BallSmooth ω)
    (hInv : ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ z : Adelic.BallNatural.Ball,
      (ω (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
          (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = ω z) :
    ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
      Continuous descended ∧
      (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
      ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z, ω z) := by
  let s : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N := Quotient.lift
    (fun z => Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z, ω z)) (by
      intro z w hzw
      obtain ⟨g,hg,hzw⟩ := (hR z w).mp hzw
      apply Quot.sound
      refine ⟨g,hg,hzw,?_⟩
      rw [← hzw]
      exact hInv g hg z)
  have hc : Continuous ω := by
    have hc := hω.continuousOn.domRestrict
    apply hc.congr
    intro z
    change (if hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1 then
      ω ⟨z.val,hz⟩ else 0) = ω z
    exact dite_eq_left z.property
  refine ⟨s, ?_, ?_, fun _ => rfl⟩
  · apply Continuous.quotient_lift
    exact continuous_quot_mk.comp (continuous_id.prodMk hc)
  · intro q
    induction q using Quotient.inductionOn with
    | h z => rfl

/-- Both finite inputs in each wedge are fixed by the displayed actual
finite-adelic subgroup, and the equality is on the common ball. -/
def FactorizationAtLevel (L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → Adelic.FiniteSchwartz.finiteSchwartz F 3),
    (∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 3 (a j) (fun i => x (Fin.castAdd 3 i)) *
        Adelic.Evaluation.finiteSchwartzFunction F 3 (b j) (fun i => x (Fin.natAdd 3 i))) ∧
    (∀ j g, g ∈ L → Adelic.FiniteSchwartz.finiteAction F H K₁ hd Q₁.characters P₁ Q₁.splittings g (a j) = a j) ∧
    (∀ j g, g ∈ L → Adelic.FiniteSchwartz.finiteAction F H S.form hd Q₂.characters P₂ Q₂.splittings g (b j) = b j) ∧
    ∀ z, IntrinsicSplitTensor.Intrinsic.splitTopForm Q₁.comparison Q₂.comparison f z =
      ∑ j, IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a j) z) (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b j) z)

theorem common_native_descent (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₁ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₁ ψ) (h₂ : IntrinsicSplitting.IntrinsicSummands.SummandValid Q₂ ψ)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form))
    (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd C P)
    (hB : Adelic.DataTheta.GeometryIdentification B) (hDesc : Adelic.DataTheta.Descent.CongruenceDescent B P hd C D)
    (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F 6)) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) hd C P D g f = f) ∧
        ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w),
          CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧
          SecondCountableTopology (Quotient R) ∧
          ∀ f ∈ Φ, FactorizationAtLevel Q₁ Q₂ L f ∧
            Adelic.BallGeometryData.BallSmooth (IntrinsicSplitTensor.Intrinsic.splitTopForm Q₁.comparison Q₂.comparison f) ∧
            ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
              Continuous descended ∧
              (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
              ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N)
                (z, IntrinsicSplitTensor.Intrinsic.splitTopForm Q₁.comparison Q₂.comparison f z) := by
  obtain ⟨_,_,_,_,_,hG₁,_,_,_,hΘ₁,_,_,hNative₁⟩ := h₁
  obtain ⟨_,_,_,_,_,hG₂,_,_,_,hΘ₂,_,_,hNative₂⟩ := h₂
  have hball₁ := total_ball_action Q₁ B hG₁ hB
  have hball₂ := (IntrinsicSplitting.IntrinsicSummands.same_ball_action A S Q₁.comparison Q₂.comparison hG₁ hG₂).symm.trans hball₁
  choose n a b hweights hforms using fun f : Adelic.FiniteSchwartz.finiteSchwartz F 6 =>
    IntrinsicSplitFactorization.Intrinsic.finite_wedge_factorization Q₁.comparison Q₂.comparison hE₁ hE₂ hTensorDecomposition hΘ₁ hΘ₂ f
  let Φ₁ := Φ.biUnion (fun f => Finset.univ.image (a f))
  let Φ₂ := Φ.biUnion (fun f => Finset.univ.image (b f))
  obtain ⟨N₁,hN₁,hdiv₁,_,L₁,_,hL₁,_,hfix₁,_⟩ :=
    hNative₁.2.2.2.2.1 Φ₁ K₀ N₀ hN₀
  obtain ⟨N₂,hN₂,hdiv₂,_,L₂,_,hL₂,_,hfix₂,_⟩ :=
    hNative₂.2.2.2.2.1 Φ₂ L₁ N₁ hN₁
  obtain ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,_⟩ :=
    hDesc Φ L₂ N₂ hN₂
  have hfixa (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (hf : f ∈ Φ) (j : Fin (n f)) (g) (hg : g ∈ L) :
      Adelic.FiniteSchwartz.finiteAction F H K₁ hd Q₁.characters P₁ Q₁.splittings g (a f j) = a f j := by
    apply hfix₁ (a f j) _ g ((hL.trans hL₂) hg)
    exact Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have hfixb (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (hf : f ∈ Φ) (j : Fin (n f)) (g) (hg : g ∈ L) :
      Adelic.FiniteSchwartz.finiteAction F H S.form hd Q₂.characters P₂ Q₂.splittings g (b f j) = b f j := by
    apply hfix₂ (b f j) _ g (hL hg)
    exact Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  refine ⟨N,hN,hdiv₁.trans (hdiv₂.trans hdiv),htf,L,hLc,(hL.trans hL₂).trans hL₁,
    hcontain,hfix,R,hR,hRc,hRt,hRs,?_⟩
  intro f hf
  have hs := IntrinsicSplitRegularity.Intrinsic.splitTopForm_smooth Q₁.comparison Q₂.comparison hE₁ hE₂ hTensorDecomposition hΘ₁ hΘ₂ f
  have hweights' : ∀ x, Adelic.Evaluation.finiteSchwartzFunction F 6 f x =
      ∑ j, Adelic.Evaluation.finiteSchwartzFunction F 3 (a f j) (fun i => x (Fin.castAdd 3 i)) *
        Adelic.Evaluation.finiteSchwartzFunction F 3 (b f j) (fun i => x (Fin.natAdd 3 i)) := by
    intro x
    simpa only [IntrinsicSchwartz.Intrinsic.productInput_value F 3 3] using hweights f x
  refine ⟨⟨n f,a f,b f,hweights',hfixa f hf,hfixb f hf,hforms f⟩,hs,?_⟩
  apply smooth_top_section B N R hR _ hs
  intro g hg z
  let gB := B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)
  let dg := fderiv ℂ (Adelic.DeterminantCoordinates.chartImage (Adelic.BallNatural.asSL gB)) z.val
  have ha (j : Fin (n f)) : (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a f j) (gB • z)).comp dg =
      OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a f j) z := by
    ext u
    have h := hNative₁.2.1 g (a f j) z u
    rw [hfixa f hf j _ (hcontain g hg), hball₁] at h
    exact h
  have hb (j : Fin (n f)) : (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b f j) (gB • z)).comp dg =
      OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b f j) z := by
    ext u
    have h := hNative₂.2.1 g (b f j) z u
    rw [hfixb f hf j _ (hcontain g hg), hball₂] at h
    exact h
  rw [hforms f, hforms f]
  have hw (j : Fin (n f)) :
      (IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a f j) (gB • z))
        (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b f j) (gB • z))).compContinuousLinearMap dg =
      IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a f j) z) (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b f j) z) := by
    rw [IntrinsicExterior.Intrinsic.wedge_naturality, ha, hb]
  ext v
  change (∑ j, IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₁.comparison (a f j) (gB • z))
    (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm Q₂.comparison (b f j) (gB • z))) (fun i => dg (v i)) = _
  simp only [ContinuousAlternatingMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun ω : IntrinsicExterior.Intrinsic.TopCovector => ω v) (hw j)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitDescent.Intrinsic
