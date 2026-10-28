import OAI.RepresentationTheory.Theta.Adelic.Data
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth

/-! # Intrinsic Compact Choices -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction

/-! Native order-two witnesses obtained from the full AdelicTheta proposition.
All the original AdelicTheta conclusions are retained, together with the proved
ordinary top-form projection, smoothness, covariance and geometric descent. -/
open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

def TopDescentConclusion (B : Adelic.DataTheta.ComparisonData F H K A)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P) : Prop :=
  ∀ (Φ : Finset (Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2))) (K₀ : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H))
    (N₀ : ℕ), 0 < N₀ →
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g →
        ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
      ∃ L : OpenSubgroup (Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
        (∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → Adelic.RationalSU.rationalFiniteSU F H g ∈ L) ∧
        (∀ f ∈ Φ, ∀ g ∈ L, Adelic.FiniteSchwartz.finiteAction F H K hd C P D g f = f) ∧
        ∃ (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w),
          CompactSpace (Quotient R) ∧ T2Space (Quotient R) ∧
          SecondCountableTopology (Quotient R) ∧
          Continuous (IntrinsicSecondDescent.Intrinsic.topProjection B N R hR) ∧
          ∀ f ∈ Φ, Adelic.BallGeometryData.BallSmooth (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f) ∧
            ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
              Continuous descended ∧
              (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
              ∀ z, descended (Quotient.mk R z) =
                Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z, IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z)

theorem construct_total (h_AdelicTheta : Adelic.Data.CompleteStatement)
    (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)
    (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) :
    ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2, C.ψ = ψ ∧ Adelic.Data.CharacterConclusion F d 3 2 C ∧
      ∃ D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hq.1 C P,
        Adelic.Data.AdelicConclusion F d 3 2 H K hq.1 C P D ∧
        Adelic.Data.FiniteConclusion F d 3 2 H K hq.1 C P D ∧
        ∃ B : Adelic.DataTheta.ComparisonData F H K A,
          Adelic.DataTheta.CoordinateIdentification B P ∧ Adelic.DataTheta.GeometryIdentification B ∧
          Adelic.DataTheta.OscillatorIdentification B P hq.1 C D ∧ Adelic.SiegelBranchData.SiegelBranchExtension B P hq.1 C D ∧
          Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hq.1 C D ∧ Adelic.DataTheta.Descent.ThetaConstruction B ∧
          Adelic.DataTheta.Descent.RationalHeckeCovariance B P hq.1 C D ∧ Adelic.DataTheta.Descent.CongruenceDescent B P hq.1 C D ∧
          (∀ f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2), Adelic.BallGeometryData.BallSmooth (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f)) ∧
          (∀ (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (z : Adelic.BallNatural.Ball),
            (IntrinsicSecondProjection.Intrinsic.thetaTopForm B (Adelic.FiniteSchwartz.finiteAction F H K hq.1 C P D (Adelic.RationalSU.rationalFiniteSU F H g) f)
              (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
                (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
                  (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z) ∧
          TopDescentConclusion B P hq.1 C D := by
  obtain ⟨C, hψ, hChar, D, hAd, hFin, B, hCoord, hGeom, hOsc, hBranch,
      hUnique, hTheta, hCov, hDesc⟩ :=
    h_AdelicTheta.2.2 F d hq 2 (Or.inr rfl) H K hH hK ψ hc hu hn hp P A hArch
  exact ⟨C, hψ, hChar, D, hAd, hFin, B, hCoord, hGeom, hOsc, hBranch,
    hUnique, hTheta, hCov, hDesc, IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth B hTheta,
    IntrinsicSecondAction.Intrinsic.thetaTopForm_covariance B P hq.1 C D hGeom hCov,
    IntrinsicSecondDescent.Intrinsic.native_top_descent B P hq.1 C D hGeom hTheta hDesc⟩

end RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic

/-! Compact-place changes of orthonormal multiplicity frames. These are
actual unitary changes of the fixed skew-Hermitian space, equal to the
identity at the distinguished place. They determine invariant positive
Hodge subspaces through the native AdelicTheta arithmetic data. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.IntrinsicSecondConstruction

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}

def multiplicityForm (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) (v : Fin A.places) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun j => if A.positive v j then Complex.I else -Complex.I)

structure CompactFrameChoice (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) where
  change : Fin A.places → (Matrix (Fin 2) (Fin 2) ℂ)ˣ
  distinguished : change A.distinguished = 1
  preserves : ∀ v,
    (change v).val.conjTranspose * multiplicityForm A v * (change v).val = multiplicityForm A v

instance (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) : TopologicalSpace (CompactFrameChoice A) :=
  TopologicalSpace.induced CompactFrameChoice.change inferInstance

def identityChoice (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) : CompactFrameChoice A where
  change _ := 1
  distinguished := rfl
  preserves _ := by simp

def choiceArithmetic (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) (p : CompactFrameChoice A) :
    Adelic.BallGeometryData.BallArithmeticData F d 2 H K :=
  { A with
    basisP := fun v => A.basisP v * p.change v
    formP := by
      intro v
      change ((A.basisP v).val * (p.change v).val).conjTranspose *
        ((Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))).map (A.complex v)) *
          ((A.basisP v).val * (p.change v).val) = _
      rw [Matrix.conjTranspose_mul]
      calc
        _ = (p.change v).val.conjTranspose *
            ((A.basisP v).val.conjTranspose *
              ((Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))).map (A.complex v)) * (A.basisP v).val) *
            (p.change v).val := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [A.formP]; exact p.preserves v }

theorem choice_distinguished_basis (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) (p : CompactFrameChoice A) :
    (choiceArithmetic A p).basisP A.distinguished = A.basisP A.distinguished := by
  change A.basisP A.distinguished * p.change A.distinguished = _
  rw [p.distinguished, mul_one]

theorem choice_standardMatrix (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) (p : CompactFrameChoice A)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    Adelic.BallGeometryData.standardMatrix (choiceArithmetic A p) g v = Adelic.BallGeometryData.standardMatrix A g v := rfl

structure TotalWitnesses (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K)
    (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K) where
  characters : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2
  splittings : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd characters P
  comparison : Adelic.DataTheta.ComparisonData F H K A

def TotalValid {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
    {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (Q : TotalWitnesses hd P A) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) : Prop :=
  Q.characters.ψ = ψ ∧ Adelic.Data.CharacterConclusion F d 3 2 Q.characters ∧
  Adelic.Data.AdelicConclusion F d 3 2 H K hd Q.characters P Q.splittings ∧
  Adelic.Data.FiniteConclusion F d 3 2 H K hd Q.characters P Q.splittings ∧
  Adelic.DataTheta.CoordinateIdentification Q.comparison P ∧ Adelic.DataTheta.GeometryIdentification Q.comparison ∧
  Adelic.DataTheta.OscillatorIdentification Q.comparison P hd Q.characters Q.splittings ∧
  Adelic.SiegelBranchData.SiegelBranchExtension Q.comparison P hd Q.characters Q.splittings ∧
  Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd Q.characters Q.splittings ∧ Adelic.DataTheta.Descent.ThetaConstruction Q.comparison ∧
  Adelic.DataTheta.Descent.RationalHeckeCovariance Q.comparison P hd Q.characters Q.splittings ∧
  Adelic.DataTheta.Descent.CongruenceDescent Q.comparison P hd Q.characters Q.splittings ∧
  IntrinsicSecondConstruction.TopDescentConclusion Q.comparison P hd Q.characters Q.splittings

theorem construct_compact_choices (h_AdelicTheta : Adelic.Data.CompleteStatement)
    (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (hn : ∃ x, ψ x ≠ 1) (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)
    (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) :
    ∃ Q : ∀ p : CompactFrameChoice A, TotalWitnesses hq.1 P (choiceArithmetic A p),
      ∀ p, TotalValid (Q p) ψ := by
  have h (p : CompactFrameChoice A) : ∃ Q : TotalWitnesses hq.1 P (choiceArithmetic A p), TotalValid Q ψ := by
    obtain ⟨C,hψ,hChar,D,hAd,hFin,B,hCoord,hGeom,hOsc,hBranch,hUnique,hTheta,hCov,hDesc,_,_,hTop⟩ :=
      IntrinsicSecondConstruction.construct_total h_AdelicTheta hq hH hK ψ hc hu hn hp P (choiceArithmetic A p) hArch
    exact ⟨⟨C,D,B⟩,hψ,hChar,hAd,hFin,hCoord,hGeom,hOsc,hBranch,hUnique,hTheta,hCov,hDesc,hTop⟩
  exact ⟨fun p => (h p).choose,fun p => (h p).choose_spec⟩

end RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic

end

end OAI
