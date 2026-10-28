import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Topology.DenseEmbedding

/-! # Dense Coefficient Ranks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DenseCoefficientRanks

noncomputable section

/-! The locally constant ranks of finite flat modules are detected after an injective coefficient extension. -/

universe u v w t

theorem coefficientSpectrum_dense {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    (f : R →+* A) (hf : Function.Injective f) : DenseRange (PrimeSpectrum.comap f) := by
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

theorem finiteFlat_rankAtStalk_dense_value
    {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    (f : R →+* A) (hf : Function.Injective f)
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
    {V : Type t} [TopologicalSpace V] [T2Space V] (v : V) (k : ℕ → V)
    (h : ∀ q : PrimeSpectrum A, k (Module.rankAtStalk (R := R) M (q.comap f)) = v)
    (p : PrimeSpectrum R) : k (Module.rankAtStalk (R := R) M p) = v := by
  have hc : Continuous (fun p : PrimeSpectrum R => k (Module.rankAtStalk (R := R) M p)) :=
    ((Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).comp k).continuous
  exact congrFun ((coefficientSpectrum_dense f hf).equalizer hc continuous_const (funext h)) p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DenseCoefficientRanks
