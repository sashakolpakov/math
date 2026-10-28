import OAI.NumberTheory.Quaternion.Arithmetic.LogTangent
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Span Local -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SpanLocal

noncomputable section

section

/-! A local logarithm at a finite place and its derivative at the identity.
The domain records both the inverse-function chart and the proven disk of
convergence for the exponential. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

def finiteLocalLog (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    A → A := (LocalCompletion.finiteExponentialChart v A).symm

@[simp] theorem finiteLocalLog_one (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    finiteLocalLog v A 1 = 0 := by
  have h := (LocalCompletion.finiteExponentialChart v A).left_inv
    (LocalCompletion.zero_mem_finiteExponentialChart_source v A)
  simpa only [finiteLocalLog, LocalCompletion.finiteExponentialChart_apply, NormedSpace.exp_zero] using h

theorem finiteLocalLog_hasStrictFDerivAt (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    HasStrictFDerivAt (finiteLocalLog v A)
      (ContinuousLinearMap.id (v.adicCompletion F) A) 1 := by
  have h := (LocalCompletion.finite_exponential_hasStrictFDerivAt v A).to_localInverse
    (f' := ContinuousLinearEquiv.refl (v.adicCompletion F) A)
  simpa only [NormedSpace.exp_zero, HasStrictFDerivAt.localInverse,
    finiteLocalLog, LocalCompletion.finiteExponentialChart, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl] using h

def finiteLogDomain (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    Set A := (LocalCompletion.finiteExponentialChart v A).target ∩
      (finiteLocalLog v A) ⁻¹' Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius

theorem finiteLogDomain_mem_nhds (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    finiteLogDomain v A ∈ 𝓝 (1 : A) := by
  apply inter_mem ((LocalCompletion.finiteExponentialChart v A).open_target.mem_nhds
    (LocalCompletion.one_mem_finiteExponentialChart_target v A))
  have h := (finiteLocalLog_hasStrictFDerivAt v A).continuousAt
  rw [ContinuousAt, finiteLocalLog_one] at h
  exact h (Metric.eball_mem_nhds _ (LocalCompletion.finite_expSeries_radius_pos v A))

theorem exp_finiteLocalLog (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    {g : A} (hg : g ∈ finiteLogDomain v A) : NormedSpace.exp (finiteLocalLog v A g) = g :=
  (LocalCompletion.finiteExponentialChart v A).right_inv hg.1

theorem finiteLocalLog_mem_tangentCone (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A]
    (H : Submonoid A) {g : A} (hg : g ∈ H) (hu : g ∈ finiteLogDomain v A) :
    finiteLocalLog v A g ∈
      tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (H : Set A) 1 := by
  apply LogTangent.local_exp_parameter_mem_tangentCone v H hu.2
  rwa [exp_finiteLocalLog v hu]

end

section

/-! The tangent span of a finite-dimensional local submonoid is generated
by its logarithms in every sufficiently small identity neighborhood. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

theorem tangentCone_subset_closed_submodule
    {κ E : Type*} [Field κ] [AddCommGroup E] [Module κ E] [TopologicalSpace E]
    (W : Submodule κ E) (hW : IsClosed (W : Set E)) {s : Set E} (hs : s ⊆ W) :
    tangentConeAt κ s 0 ⊆ (W : Set E) := by
  intro X hX
  obtain ⟨α, l, hl, c, d, hd, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hX
  apply hW.mem_of_tendsto hcd
  filter_upwards [hds] with j hj
  exact W.smul_mem (c j) (hs (by simpa only [zero_add] using hj))

variable {F : Type} [Field F] [NumberField F]

theorem tangentSpan_eq_span_localLog (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [NormedAlgebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    (H : Submonoid A) {U : Set A} (hU : U ∈ 𝓝 (1 : A))
    (hUsmall : U ⊆ finiteLogDomain v A) :
    Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        (tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (H : Set A) 1) =
      Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        (finiteLocalLog v A '' ((H : Set A) ∩ U)) := by
  let : NontriviallyNormedField (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :=
    TangentBracket.finiteClosedPrimeNontriviallyNormedField v
  let W := Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
    (finiteLocalLog v A '' ((H : Set A) ∩ U))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro X hX
    have hXi : X ∈ tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        ((H : Set A) ∩ U) 1 := by
      rwa [tangentConeAt_inter_nhds hU]
    obtain ⟨α, l, hl, c, d, hd, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hXi
    let cK := fun j => algebraMap (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (v.adicCompletion F) (c j)
    have hec (j : α) (Y : A) : cK j • Y = c j • Y :=
      IsScalarTower.algebraMap_smul (v.adicCompletion F) (c j) Y
    have hcdK : Tendsto (fun j => cK j • d j) l (𝓝 X) := by
      simpa only [hec] using hcd
    have hlim := (finiteLocalLog_hasStrictFDerivAt v A).hasFDerivAt.hasFDerivWithinAt
      (s := (H : Set A) ∩ U) |>.lim hd hds hcdK
    have hloglim : Tendsto (fun j => c j • finiteLocalLog v A (1 + d j)) l (𝓝 X) := by
      simpa only [finiteLocalLog_one, sub_zero, ContinuousLinearMap.id_apply, hec] using hlim
    apply W.closed_of_finiteDimensional.mem_of_tendsto hloglim
    filter_upwards [hds] with j hj
    exact W.smul_mem (c j) (Submodule.subset_span ⟨1 + d j, hj, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, ⟨hg, hu⟩, rfl⟩
    exact Submodule.subset_span (finiteLocalLog_mem_tangentCone v H hg (hUsmall hu))

end

/-! A finite basis selected from a prescribed spanning set. This will
select genuine local subgroup logarithms for the analytic coordinates. -/

open scoped Classical
open Set _root_.Module

theorem exists_fin_basis_span_mem
    {κ E : Type*} [Field κ] [AddCommGroup E] [Module κ E] [FiniteDimensional κ E]
    (s : Set E) :
    ∃ (n : ℕ) (b : Basis (Fin n) κ (Submodule.span κ s)), ∀ i, (b i : E) ∈ s := by
  let t : Set (Submodule.span κ s) := Subtype.val ⁻¹' s
  have ht : ⊤ ≤ Submodule.span κ t := by
    rw [show t = Subtype.val ⁻¹' s from rfl, Submodule.span_span_coe_preimage]
  let b := Basis.ofSpan ht
  let := FiniteDimensional.fintypeBasisIndex b
  refine ⟨Fintype.card _, b.reindex (Fintype.equivFin _), ?_⟩
  intro i
  have h := Basis.ofSpan_subset ht
    (mem_range_self (f := b) ((Fintype.equivFin _).symm i))
  simpa only [Basis.reindex_apply, t, mem_preimage] using h

end

end OAI.NumberTheory.Quaternion.Arithmetic.SpanLocal
