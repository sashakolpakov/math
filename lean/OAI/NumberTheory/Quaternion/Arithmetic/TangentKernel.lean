import OAI.NumberTheory.Quaternion.Arithmetic.ExponentialTransport
import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding
import OAI.NumberTheory.Quaternion.Arithmetic.LocalSubgroup

/-! # Tangent Kernel -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TangentKernel

noncomputable section

/-! If a ring projection kills all subgroup tangent directions, then it
is identically one on the subgroup near the identity. A closed regular
representation lets the source use its original local topologies. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain NormedSpace Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem tangent_kernel_implies_locally_trivial (v : HeightOneSpectrum (𝓞 F))
    {A D B : Type*} [Ring A] [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [NormedRing D] [NormedAlgebra (v.adicCompletion F) D] [CompleteSpace D]
    [Ring B] [Algebra ℚ B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]
    (f : A →ₐ[TangentBracket.closedPrimeSubfield (v.adicCompletion F)] D) (hf : IsClosedEmbedding f)
    (π : A →+* B) (hπ : Continuous π) (H : Submonoid A)
    (hker : ∀ a : A, f a ∈ LocalSubgroup.primeLocalTangentSpan v (H.map f.toMonoidHom) → π a = 0) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ H → π g = 1 := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F _
  let : IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) D :=
    OrderedProductDerivative.finitePrimeScalarTower v D
  have hs : LocalSubgroup.primeLocalTangentSpan v (H.map f.toMonoidHom) ≤ f.toLinearMap.range := by
    apply Submodule.span_le.mpr
    apply RegularMatrixEmbedding.tangentCone_subset_closed_submodule_at f.toLinearMap.range hf.isClosed_range
    · rintro _ ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
    · exact ⟨1, map_one f⟩
  have ht := hf.continuous.tendsto (1 : A)
  rw [map_one] at ht
  have hn : ∀ᶠ g in 𝓝 (1 : A), f g ∈ SpanLocal.finiteLogDomain v D := ht (SpanLocal.finiteLogDomain_mem_nhds v D)
  filter_upwards [hn] with g hg
  intro hgH
  have hlog : SpanLocal.finiteLocalLog v D (f g) ∈ LocalSubgroup.primeLocalTangentSpan v (H.map f.toMonoidHom) :=
    Submodule.subset_span (SpanLocal.finiteLocalLog_mem_tangentCone v (H.map f.toMonoidHom) ⟨g, hgH, rfl⟩ hg)
  obtain ⟨a, ha⟩ := hs hlog
  have hsmall : f a ∈ Metric.eball 0 (expSeries (v.adicCompletion F) D).radius := ha.symm ▸ hg.2
  have hfa : f (exp a) = f g := by
    calc
      f (exp a) = exp (f a) := ExponentialTransport.map_exp_of_closed_embedding f.toRingHom hf a hsmall
      _ = exp (SpanLocal.finiteLocalLog v D (f g)) := congrArg exp ha
      _ = f g := SpanLocal.exp_finiteLocalLog v hg
  have he : exp a = g := hf.injective hfa
  have hz : π a = 0 := hker a (ha.symm ▸ hlog)
  rw [← he, ExponentialTransport.map_exp_of_summable π hπ a
    (ExponentialTransport.exp_series_summable_of_closed_embedding f.toRingHom hf a hsmall), hz, exp_zero]

end

end OAI.NumberTheory.Quaternion.Arithmetic.TangentKernel
