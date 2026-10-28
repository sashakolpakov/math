import OAI.RepresentationTheory.Weil.UnitarySplitting.Weighted
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates
import OAI.RepresentationTheory.Weil.UnitarySplitting.FormScaling

/-! # Assembly -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Assembly.Construction

noncomputable section

/-! Transport of centralizer statements and assembly of commuting splittings. -/

theorem unitaryScaleForm_continuous
    {F E I : Type} [Field F] [NormedField E] [Algebra F E]
    [Fintype I] [DecidableEq I] (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (z : E) :
    Continuous (FormScaling.Construction.unitaryScaleForm σ Q z) :=
  continuous_subtype_val.subtype_mk _

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ)

theorem frameSplitting_centralizer [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    {G : Type} [Group G]
    (α : G →* FrameTransport.Construction.StandardSymplectic F (m * n)) (s : G →* Oscillator.Construction.CircleExtension σ H K c ψ)
    (hs : ∀ (k : FrameTransport.Construction.StandardSymplectic F (m * n)) (b : Oscillator.Construction.CircleExtension σ H K c ψ),
      Oscillator.Construction.circleProjection σ H K c ψ b = FrameTransport.Construction.frameSymplectic σ H K c k →
      (∀ g, Commute (α g) k) → ∀ g, Commute (s g) b)
    (b : Oscillator.Construction.CircleExtension σ H K c ψ)
    (hb : ∀ g, Commute (FrameTransport.Construction.frameSymplectic σ H K c (α g)) (Oscillator.Construction.circleProjection σ H K c ψ b)) :
    ∀ g, Commute (s g) b := by
  obtain ⟨k, hk⟩ := UltraSurjectivity.Construction.frameSymplectic_surjective σ H K c (Oscillator.Construction.circleProjection σ H K c ψ b)
  apply hs k b hk.symm
  intro g
  apply (TensorFrameCoordinates.Construction.frameSymplectic_injective σ H K c)
  rw [map_mul, map_mul, hk]
  exact (hb g).eq

theorem dualPair_factors_commute (g : DualPair.Construction.unitaryGroup σ H) (h : DualPair.Construction.unitaryGroup σ K) :
    Commute (DualPair.Construction.dualPairAction σ H K (g, 1)) (DualPair.Construction.dualPairAction σ H K (1, h)) := by
  change DualPair.Construction.dualPairAction σ H K (g, 1) * DualPair.Construction.dualPairAction σ H K (1, h) = _
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]

def commutingProductHom {G J A : Type} [Group G] [Group J] [Group A]
    [TopologicalSpace G] [TopologicalSpace J] [TopologicalSpace A] [ContinuousMul A]
    (s : G →ₜ* A) (t : J →ₜ* A) (hcomm : ∀ g h, Commute (s g) (t h)) :
    (G × J) →ₜ* A where
  toFun x := s x.1 * t x.2
  map_one' := by
    change s 1 * t 1 = 1
    simp only [map_one, one_mul]
  map_mul' x y := by
    change s (x.1 * y.1) * t (x.2 * y.2) = _
    rw [map_mul, map_mul]
    calc
      (s x.1 * s y.1) * (t x.2 * t y.2) = s x.1 * (s y.1 * t x.2) * t y.2 := by simp only [mul_assoc]
      _ = s x.1 * (t x.2 * s y.1) * t y.2 := by rw [(hcomm y.1 x.2).eq]
      _ = (s x.1 * t x.2) * (s y.1 * t y.2) := by simp only [mul_assoc]
  continuous_toFun := (s.continuous.comp continuous_fst).mul (t.continuous.comp continuous_snd)

theorem dualPairSplitting_assembly [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    [IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ)]
    (s : DualPair.Construction.unitaryGroup σ H →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ)
    (t : DualPair.Construction.unitaryGroup σ K →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ)
    (hs : ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (s g) = DualPair.Construction.dualPairAction σ H K (g, 1))
    (ht : ∀ h, Oscillator.Construction.circleProjection σ H K c ψ (t h) = DualPair.Construction.dualPairAction σ H K (1, h))
    (hcentral : ∀ b : Oscillator.Construction.CircleExtension σ H K c ψ,
      (∀ g, Commute (DualPair.Construction.dualPairAction σ H K (g, 1)) (Oscillator.Construction.circleProjection σ H K c ψ b)) →
      ∀ g, Commute (s g) b) :
    ∃ splitting : (DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K) →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (splitting g) = DualPair.Construction.continuousDualPairAction σ H K g := by
  have hh : ∀ g h, Commute (s g) (t h) := by
    intro g h
    apply hcentral (t h) _ g
    intro k
    rw [ht]
    exact dualPair_factors_commute σ H K k h
  refine ⟨commutingProductHom s t hh, ?_⟩
  intro g
  change Oscillator.Construction.circleProjection σ H K c ψ (s g.1 * t g.2) = _
  rw [map_mul, hs, ht, ← map_mul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]
  rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Assembly.Construction
