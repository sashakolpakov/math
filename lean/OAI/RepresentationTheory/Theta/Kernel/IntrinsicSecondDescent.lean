import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction

/-! # Intrinsic Second Descent -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic

noncomputable section

/-! Descent through the actual top-covector orbit quotient. The map from
the symmetric Hodge tensor quotient is induced by the twice alternating
projection and is proved continuous. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.IntrinsicTransport

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

def TopOrbit (N : ℕ) (p q : Adelic.BallNatural.Ball × IntrinsicExterior.Intrinsic.TopCovector) : Prop :=
  ∃ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g ∧
    B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • p.1 = q.1 ∧
    q.2.compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
        (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) p.1.val) = p.2

abbrev TopBundle (N : ℕ) := Quot (TopOrbit B N)

def topProjection (N : ℕ) (R : Setoid Adelic.BallNatural.Ball)
    (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w) : TopBundle B N → Quotient R :=
  Quot.lift (fun p : Adelic.BallNatural.Ball × IntrinsicExterior.Intrinsic.TopCovector => Quotient.mk R p.1) (by
    intro p q hpq
    obtain ⟨g, hg, hb, _⟩ := hpq
    exact Quotient.sound ((hR p.1 q.1).mpr ⟨g, hg, hb⟩))

theorem topProjection_continuous (N : ℕ) (R : Setoid Adelic.BallNatural.Ball)
    (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w) :
    Continuous (topProjection B N R hR) :=
  continuous_quot_lift _ (continuous_quotient_mk'.comp continuous_fst)

def tensorProjection (hGeometry : Adelic.DataTheta.GeometryIdentification B) (N : ℕ)
    (S : Setoid (Adelic.BallNatural.Ball × Adelic.DataTheta.Descent.SymmetricTensor (A := A) 2))
    (hS : ∀ p q, S.r p q ↔ Adelic.DataTheta.Descent.TensorOrbit B N 2 p q) : Quotient S → TopBundle B N :=
  Quotient.lift (fun p => Quot.mk (TopOrbit B N) (p.1, IntrinsicSecondProjection.Intrinsic.secondProjection p.2.val)) (by
    intro p q hpq
    obtain ⟨g, hg, hb, ht⟩ := (hS p q).mp hpq
    apply Quot.sound
    exact ⟨g, hg, hb, IntrinsicSecondAction.IntrinsicTransport.secondProjection_transport B hGeometry
      (Adelic.RationalSU.rationalArchimedeanSU F H g) p.1 p.2.val q.2.val ht⟩)

theorem tensorProjection_continuous (hGeometry : Adelic.DataTheta.GeometryIdentification B) (N : ℕ)
    (S : Setoid (Adelic.BallNatural.Ball × Adelic.DataTheta.Descent.SymmetricTensor (A := A) 2))
    (hS : ∀ p q, S.r p q ↔ Adelic.DataTheta.Descent.TensorOrbit B N 2 p q) :
    Continuous (tensorProjection B hGeometry N S hS) := by
  apply Continuous.quotient_lift
  apply continuous_quot_mk.comp
  exact continuous_fst.prodMk ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).continuous.comp
    (continuous_subtype_val.comp continuous_snd))

theorem tensorProjection_over (hGeometry : Adelic.DataTheta.GeometryIdentification B) (N : ℕ)
    (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w)
    (S : Setoid (Adelic.BallNatural.Ball × Adelic.DataTheta.Descent.SymmetricTensor (A := A) 2))
    (hS : ∀ p q, S.r p q ↔ Adelic.DataTheta.Descent.TensorOrbit B N 2 p q)
    (projection : Quotient S → Quotient R)
    (hprojection : ∀ p, projection (Quotient.mk S p) = Quotient.mk R p.1)
    (q : Quotient S) :
    topProjection B N R hR (tensorProjection B hGeometry N S hS q) = projection q := by
  induction q using Quotient.inductionOn with
  | h p => exact (hprojection p).symm

/-- Every finite input family descends at one native principal level to
the ordinary top-covector quotient, with smooth representatives on the ball. -/
theorem native_top_descent
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P)
    (hGeometry : Adelic.DataTheta.GeometryIdentification B) (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B)
    (hDescent : Adelic.DataTheta.Descent.CongruenceDescent B P hd C D)
    (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2))) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g →
        ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧
        ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w),
          CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧
          SecondCountableTopology (Quotient R) ∧
          Continuous (topProjection B N R hR) ∧
          ∀ f ∈ Φ, Adelic.BallGeometryData.BallSmooth (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f) ∧
            ∃ descended : Quotient R → TopBundle B N,
              Continuous descended ∧
              (∀ q, topProjection B N R hR (descended q) = q) ∧
              ∀ z, descended (Quotient.mk R z) =
                Quot.mk (TopOrbit B N) (z, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z) := by
  obtain ⟨N, hN, hdiv, htf, L, hL, hLK, hcontain, hfix, R, hR,
    hcompact, hHausdorff, hcountable, htensors⟩ := hDescent Φ K₀ N₀ hN₀
  obtain ⟨S, hS, projection, _, hprojection, hsections⟩ := htensors 2
  refine ⟨N, hN, hdiv, htf, L, hL, hLK, hcontain, hfix, R, hR,
    hcompact, hHausdorff, hcountable, topProjection_continuous B N R hR, ?_⟩
  intro f hf
  obtain ⟨T, hT, descended, hcont, hsection, hvalue⟩ := hsections f hf
  refine ⟨IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth B hTheta f,
    tensorProjection B hGeometry N S hS ∘ descended,
    (tensorProjection_continuous B hGeometry N S hS).comp hcont, ?_, ?_⟩
  · intro q
    exact (tensorProjection_over B hGeometry N R hR S hS projection hprojection _).trans
      (hsection q)
  · intro z
    change tensorProjection B hGeometry N S hS (descended (Quotient.mk R z)) = _
    rw [hvalue]
    change Quot.mk _ (z, IntrinsicSecondProjection.Intrinsic.secondProjection (T z).val) = _
    rw [hT]
    rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic
