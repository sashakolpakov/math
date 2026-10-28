import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedRegularJet
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetProduct

/-! # Jet Ideal Generators -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetIdealGenerators

noncomputable section

/-! A spanning family of first-order data produces generators of
the maximal ideal after subtracting its values along a chosen nonzero coordinate. -/

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedCotangent

universe u v w

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
  (ε : R →ₐ[K] K) (r : R)

def centered : R →ₗ[K] AugmentedCotangent.ideal ε :=
  ε r • AugmentedCotangent.center ε - LinearMap.smulRight ε.toLinearMap (AugmentedCotangent.center ε r)

theorem centered_val (s : R) :
    (centered ε r s).val = ε r • s - ε s • r := by
  change ε r • (s - algebraMap K R (ε s)) - ε s • (r - algebraMap K R (ε r)) = _
  simp only [Algebra.smul_def]
  ring

def cotangentMap : (K × (AugmentedCotangent.ideal ε).Cotangent) →ₗ[K] (AugmentedCotangent.ideal ε).Cotangent :=
  ε r • LinearMap.snd K K (AugmentedCotangent.ideal ε).Cotangent -
    LinearMap.smulRight (LinearMap.fst K K (AugmentedCotangent.ideal ε).Cotangent) (AugmentedCotangent.differential ε r)

theorem cotangentMap_jet (s : R) :
    cotangentMap ε r (AugmentedCotangent.jet ε s) = (AugmentedCotangent.ideal ε).toCotangent (centered ε r s) := by
  change ε r • (AugmentedCotangent.ideal ε).toCotangent (AugmentedCotangent.center ε s) - ε s • (AugmentedCotangent.ideal ε).toCotangent (AugmentedCotangent.center ε r) = _
  exact (((AugmentedCotangent.ideal ε).toCotangent.restrictScalars K).map_sub
    (ε r • AugmentedCotangent.center ε s) (ε s • AugmentedCotangent.center ε r)).symm

theorem cotangentMap_surjective (hr : ε r ≠ 0) : Function.Surjective (cotangentMap ε r) := by
  intro v
  refine ⟨(0, (ε r)⁻¹ • v), ?_⟩
  change ε r • ((ε r)⁻¹ • v) - (0 : K) • AugmentedCotangent.differential ε r = v
  simp [smul_smul, hr]

theorem span_cotangent {ι : Type w} (s : ι → R) (hr : ε r ≠ 0)
    (hs : Submodule.span K (Set.range (fun a => AugmentedCotangent.jet ε (s a))) = ⊤) :
    Submodule.span K (Set.range (fun a => (AugmentedCotangent.ideal ε).toCotangent (centered ε r (s a)))) = ⊤ := by
  have h := congrArg (Submodule.map (cotangentMap ε r)) hs
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr (cotangentMap_surjective ε r hr)] at h
  simpa only [← Set.range_comp, Function.comp_def, cotangentMap_jet] using h

theorem map_top_iff [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I = IsLocalRing.maximalIdeal R) (M : Submodule R I) :
    M.map I.toCotangent = ⊤ ↔ M = ⊤ := by
  subst I
  exact IsLocalRing.CotangentSpace.map_eq_top_iff

theorem span_maximalIdeal [IsNoetherianRing R] [IsLocalRing R]
    {ι : Type w} (s : ι → R) (hr : ε r ≠ 0)
    (hs : Submodule.span K (Set.range (fun a => AugmentedCotangent.jet ε (s a))) = ⊤) :
    Ideal.span (Set.range (fun a => ε r • s a - ε (s a) • r)) = IsLocalRing.maximalIdeal R := by
  let M := Submodule.span R (Set.range (fun a => centered ε r (s a)))
  have hM : M.map (AugmentedCotangent.ideal ε).toCotangent = ⊤ := by
    apply (Submodule.restrictScalars_eq_top_iff K R (AugmentedCotangent.ideal ε).Cotangent).mp
    rw [← top_le_iff, ← span_cotangent ε r s hr hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, rfl⟩)
  have htop := (map_top_iff (AugmentedCotangent.ideal ε) (AugmentedRegularJet.ideal_eq ε) M).mp hM
  have h := congrArg (Submodule.map (AugmentedCotangent.ideal ε).subtype) htop
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
  rw [← AugmentedRegularJet.ideal_eq ε]
  simpa only [← Set.range_comp, Function.comp_def, Submodule.subtype_apply, centered_val] using h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.JetIdealGenerators
