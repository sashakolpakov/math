import OAI.NumberTheory.Quaternion.Arithmetic.TangentKernel
import OAI.NumberTheory.Quaternion.Arithmetic.CompactFactorProjection

/-! # Nonzero Tangent Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NonzeroTangentProjection

noncomputable section

/-! A nondiscrete projection across compact other factors contributes a
nonzero projected tangent direction in a closed regular representation. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem compact_projection_has_nonzero_tangent (v : HeightOneSpectrum (𝓞 F))
    {A D B C L : Type*}
    [Ring A] [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [NormedRing D] [NormedAlgebra (v.adicCompletion F) D] [CompleteSpace D]
    [Ring B] [Algebra ℚ B] [TopologicalSpace B] [IsTopologicalRing B] [T2Space B]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [T2Space L]
    (f : A →ₐ[TangentBracket.closedPrimeSubfield (v.adicCompletion F)] D) (hf : IsClosedEmbedding f)
    (π : A →+* B) (hπ : Continuous π)
    (e : C × L →* A) (he : Continuous e)
    (j : L →* B) (hj : Function.Injective j) (hproj : ∀ x : C × L, π (e x) = j x.2)
    (H : Subgroup (C × L)) (hH : IsClosed (H : Set (C × L)))
    (hnd : ¬ IsDiscrete (H.map (MonoidHom.snd C L) : Set L)) :
    ∃ a : A, f a ∈ LocalSubgroup.primeLocalTangentSpan v ((H.toSubmonoid.map e).map f.toMonoidHom) ∧ π a ≠ 0 := by
  by_contra h
  push Not at h
  have hn := TangentKernel.tangent_kernel_implies_locally_trivial v f hf π hπ (H.toSubmonoid.map e) h
  have ht := he.tendsto (1 : C × L)
  rw [map_one] at ht
  have hlocal : ∀ᶠ x in 𝓝 (1 : C × L), x ∈ H → x.2 = 1 := by
    filter_upwards [ht hn] with x hx
    intro hxH
    have hz : π (e x) = 1 := hx ⟨x, hxH, rfl⟩
    apply hj
    rw [map_one, ← hproj]
    exact hz
  exact hnd (CompactFactorProjection.compact_factor_projection_discrete_of_locally_trivial H hH hlocal)

end

end OAI.NumberTheory.Quaternion.Arithmetic.NonzeroTangentProjection
