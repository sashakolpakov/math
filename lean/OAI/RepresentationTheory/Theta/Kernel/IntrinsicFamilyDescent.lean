import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices

/-! # Intrinsic Family Descent -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent.IntrinsicFamily

noncomputable section

/-! Descent of a proved invariant family of ordinary top forms at one
native total finite level. The compact-family application derives both
smoothness and invariance from the complete AdelicTheta conclusions. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P)
variable {T : Type} (ω : T → Adelic.FiniteSchwartz.finiteSchwartz F 6 → Adelic.BallNatural.Ball → IntrinsicExterior.Intrinsic.TopCovector)

theorem native_smooth_top_section (N : ℕ) (R : Setoid Adelic.BallNatural.Ball)
    (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w)
    (η : Adelic.BallNatural.Ball → IntrinsicExterior.Intrinsic.TopCovector) (hη : Adelic.BallGeometryData.BallSmooth η)
    (hi : ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ z : Adelic.BallNatural.Ball,
      (η (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
          (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = η z) :
    ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
      Continuous descended ∧ (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
      ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z,η z) := by
  let σ : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N := Quotient.lift
    (fun z => Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z,η z)) (by
      intro z w hzw
      obtain ⟨g,hg,hzw⟩ := (hR z w).mp hzw
      apply Quot.sound
      refine ⟨g,hg,hzw,?_⟩
      rw [← hzw]
      exact hi g hg z)
  have hc : Continuous η := by
    have h := hη.continuousOn.domRestrict
    apply h.congr
    intro z
    change (if hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < 1 then
      η ⟨z.val,hz⟩ else 0) = η z
    exact dite_eq_left z.property
  refine ⟨σ,?_,?_,fun _ => rfl⟩
  · apply Continuous.quotient_lift
    exact continuous_quot_mk.comp (continuous_id.prodMk hc)
  · intro q
    induction q using Quotient.inductionOn with
    | h z => rfl

def FamilyTopDescent : Prop :=
  ∀ (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F 6)) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H)) (N₀ : ℕ), 0 < N₀ →
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧
        ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w),
          CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧ SecondCountableTopology (Quotient R) ∧
          ∀ (p : T) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6), f ∈ Φ → Adelic.BallGeometryData.BallSmooth (ω p f) ∧
            ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
              Continuous descended ∧ (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
              ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z,ω p f z)

theorem family_descent (hTop : IntrinsicCompactChoices.IntrinsicSecondConstruction.TopDescentConclusion B P hd C D)
    (hs : ∀ p f, Adelic.BallGeometryData.BallSmooth (ω p f))
    (hi : ∀ p (g : Adelic.SpecialUnitary.SU H.val) f,
      Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f → ∀ z : Adelic.BallNatural.Ball,
      (ω p f (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
          (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = ω p f z) :
    FamilyTopDescent B P hd C D ω := by
  intro Φ K₀ N₀ hN₀
  obtain ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,_,_⟩ := hTop Φ K₀ N₀ hN₀
  refine ⟨N,hN,hdiv,htf,L,hLc,hL,hcontain,hfix,R,hR,hRc,hRt,hRs,?_⟩
  intro p f hf
  refine ⟨hs p f,?_⟩
  apply native_smooth_top_section B N R hR _ (hs p f)
  intro g hg z
  exact hi p g f (hfix f hf _ (hcontain g hg)) z

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent.IntrinsicFamily
