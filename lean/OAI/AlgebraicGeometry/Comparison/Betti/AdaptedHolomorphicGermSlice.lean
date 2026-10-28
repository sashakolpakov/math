import OAI.AlgebraicGeometry.Comparison.Betti.LocalGermEquivRepresentatives
import OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.NormalSlice

/-! # Adapted Holomorphic Germ Slice -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdaptedHolomorphicGermSlice.AnalyticLocal

noncomputable section

section

/-! Adapted holomorphic coordinates identify the original germ pullback with restriction to a normal slice. -/

open Set Filter
open scoped _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}
  (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x) (y : F) (hfy : f x = y)
  (e : OpenPartialHomeomorph F (E × (Fin n → ℂ)))
  (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
  (hy : y ∈ e.source) (z : Fin n → ℂ) (hey : e y = (x, z))
  (hcoords : (fun u => e (f u)) =ᶠ[𝓝 x] (fun u => (u, z)))

omit [FiniteDimensional ℂ E] in
include hcoords in
theorem adaptedHolomorphicGermSlice_square :
    (Finite.NormalSlice.AnalyticLocal.normalSliceEvaluation x z).comp (LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt e he hi y hy (x, z) hey).toRingHom =
      LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt f x hf y hfy := by
  apply RingHom.ext
  intro a
  obtain ⟨v, hva, _⟩ := a.property
  have hv := LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt_representative e he hi y hy (x, z) hey a v hva.symm
  have hsource : ∀ᶠ u in 𝓝 x, f u ∈ e.source :=
    hf.continuousAt (e.open_source.mem_nhds (hfy.symm ▸ hy))
  apply Subtype.ext
  change GermComposition.AnalyticLocal.germComposition (fun u : E => (u, z)) _
    (LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt e he hi y hy (x, z) hey a).val =
      (LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt f x hf y hfy a).val
  rw [hv, LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt_val, ← hva]
  apply Germ.coe_eq.mpr
  filter_upwards [hsource, hcoords] with u hu hcu
  apply congrArg v
  change e.symm (u, z) = f u
  rw [← hcu]
  exact e.left_inv hu

include hcoords in
theorem adaptedHolomorphicGermSlice_kernel :
    RingHom.ker (LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt f x hf y hfy) =
      Ideal.comap (LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt e he hi y hy (x, z) hey).toRingHom
        (Ideal.span (Set.range (Finite.NormalSlice.AnalyticLocal.normalCoordinateGerm x z))) := by
  rw [← adaptedHolomorphicGermSlice_square f x hf y hfy e he hi hy z hey hcoords,
    ← Finite.NormalSlice.AnalyticLocal.normalSliceEvaluation_ker n x z]
  rfl

end

/-! The normal functions of adapted holomorphic coordinates generate the original pullback kernel. -/

open Set Filter
open scoped _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}

def adaptedNormalCoordinateGerm (e : OpenPartialHomeomorph F (E × (Fin n → ℂ)))
    (he : DifferentiableOn ℂ e e.source) (y : F) (hy : y ∈ e.source) (z : Fin n → ℂ) (i : Fin n) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y :=
  ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction y (fun p : F => (e p).2 i - z i) e.open_source hy (by
    have h₁ : DifferentiableOn ℂ (fun p : F => (e p).2) e.source := he.snd
    have h₂ : DifferentiableOn ℂ (fun p : F => (e p).2 i) e.source :=
      (show Differentiable ℂ (fun w : Fin n → ℂ => w i) from differentiable_apply i).comp_differentiableOn h₁
    exact h₂.sub_const (z i))

theorem localHolomorphicGermEquivAt_symm_normal
    (e : OpenPartialHomeomorph F (E × (Fin n → ℂ)))
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (y : F) (hy : y ∈ e.source) (x : E) (z : Fin n → ℂ) (hey : e y = (x, z)) (i : Fin n) :
    (LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt e he hi y hy (x, z) hey).symm (Finite.NormalSlice.AnalyticLocal.normalCoordinateGerm x z i) =
      adaptedNormalCoordinateGerm e he y hy z i := by
  apply Subtype.ext
  erw [LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt_symm_val, Finite.NormalSlice.AnalyticLocal.normalCoordinateGerm_val]
  rfl

variable [FiniteDimensional ℂ E]

theorem adaptedHolomorphicGermSlice_kernel_le
    (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x) (y : F) (hfy : f x = y)
    (e : OpenPartialHomeomorph F (E × (Fin n → ℂ)))
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (hy : y ∈ e.source) (z : Fin n → ℂ) (hey : e y = (x, z))
    (hcoords : (fun u => e (f u)) =ᶠ[𝓝 x] (fun u => (u, z)))
    (J : Ideal (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y))
    (hJ : ∀ i, adaptedNormalCoordinateGerm e he y hy z i ∈ J) :
    RingHom.ker (LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt f x hf y hfy) ≤ J := by
  let H := LocalGermEquivRepresentatives.Analytic.localHolomorphicGermEquivAt e he hi y hy (x, z) hey
  let I := Ideal.map H.toRingHom J
  have hI (i : Fin n) : Finite.NormalSlice.AnalyticLocal.normalCoordinateGerm x z i ∈ I := by
    have h := Ideal.mem_map_of_mem H.toRingHom (hJ i)
    have hn : H (adaptedNormalCoordinateGerm e he y hy z i) = Finite.NormalSlice.AnalyticLocal.normalCoordinateGerm x z i := by
      rw [← localHolomorphicGermEquivAt_symm_normal e he hi y hy x z hey i]
      exact H.apply_symm_apply _
    exact hn ▸ h
  intro a ha
  have hs : Finite.NormalSlice.AnalyticLocal.normalSliceEvaluation x z (H a) = 0 :=
    (RingHom.congr_fun (adaptedHolomorphicGermSlice_square f x hf y hfy e he hi hy z hey hcoords) a).trans ha
  have hmem : H a ∈ I := Finite.NormalSlice.AnalyticLocal.normalSlice_zero_mem_ideal n x z I hI (H a) hs
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective H.toRingHom H.surjective).mp hmem
  exact H.injective hba ▸ hb

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdaptedHolomorphicGermSlice.AnalyticLocal
