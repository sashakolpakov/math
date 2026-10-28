import OAI.RepresentationTheory.Theta.Geometric.CompactInjectiveLinearImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization

/-! # Compact Analytic Image -/

namespace OAI.RepresentationTheory.Theta.Geometric.CompactAnalyticImage

noncomputable section

section

/-! A compact set with a finite fiber has a locally analytic linear image
when the points of that fiber have local holomorphic equations. -/

open Set
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization.Constructions.Cone

theorem compact_finite_linear_image_coordinates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (n : ℕ) : ∀ {S : Set (Fin n → ℂ)}, IsCompact S →
      ∀ (L : (Fin n → ℂ) →L[ℂ] F) (y : F),
      {v | v ∈ S ∧ L v = y}.Finite →
      (∀ v ∈ S, L v = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  classical
  induction n with
  | zero =>
    intro S hS L y _ hlocal
    exact CompactInjectiveLinearImage.compact_injective_linear_image_local hS L (fun _ _ _ => Subsingleton.elim _ _) y hlocal
  | succ n ih =>
    intro S hS L y hfinite hlocal
    by_cases hL : Function.Injective L
    · exact CompactInjectiveLinearImage.compact_injective_linear_image_local hS L hL y hlocal
    obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hL
    have hv0 : u - v ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    change (u - v) i ≠ 0 at hi
    let w := ((u - v) i)⁻¹ • (u - v)
    have hw : w i = 1 := by
      change ((u - v) i)⁻¹ * (u - v) i = 1
      exact inv_mul_cancel₀ hi
    have hLw : L w = 0 := by simp [w, map_sub, huv]
    let b := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization.Constructions.Cone.omittedCoordinateEquiv i
    let e := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv i w
    let Q := b.toContinuousLinearMap.comp (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection.Constructions.Segre.projectionAlong i w)
    let T := Q '' S
    let R := e.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℂ _ ℂ).comp b.symm.toContinuousLinearMap)
    let L' := L.comp R
    have hsection (a : Fin (n + 1) → ℂ) :
        e.symm (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection.Constructions.Segre.projectionAlong i w a, 0) = a - a i • w := by
      ext j
      by_cases hj : j = i
      · simp [e, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv, hj, hw]
      · simp [e, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection.Constructions.Segre.projectionAlong, hj]
    have hfactor (a : Fin (n + 1) → ℂ) : L' (Q a) = L a := by
      change L (e.symm (b.symm (b (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection.Constructions.Segre.projectionAlong i w a)), 0)) = L a
      rw [b.symm_apply_apply, hsection, map_sub, map_smul, hLw, smul_zero, sub_zero]
    let : CompactSpace S := isCompact_iff_compactSpace.mp hS
    have hproper : IsProperMap (fun a : S => Q a) :=
      (Q.continuous.comp continuous_subtype_val).isProperMap
    have hcompactT : IsCompact T := hS.image Q.continuous
    have hfiniteT : {a | a ∈ T ∧ L' a = y}.Finite := by
      apply (hfinite.image Q).subset
      rintro a ⟨⟨v, hv, rfl⟩, ha⟩
      exact ⟨v, ⟨hv, by rwa [hfactor] at ha⟩, rfl⟩
    have hlocalT : ∀ a ∈ T, L' a = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T a := by
      intro a _ ha
      let e' : (Fin (n + 1) → ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
        e.trans (b.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ))
      have he' (v : Fin (n + 1) → ℂ) : (e' v).1 = Q v := rfl
      have hfin : {v | v ∈ S ∧ (e' v).1 = a}.Finite := hfinite.subset (by
        rintro v ⟨hv, hva⟩
        refine ⟨hv, ?_⟩
        rw [← hfactor, ← he', hva, ha])
      have hloc : ∀ v ∈ S, (e' v).1 = a → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v := by
        intro v hv hva
        apply hlocal v hv
        rw [← hfactor, ← he', hva, ha]
      exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_linear_projection e' hproper hfin hloc
    have himage : L' '' T = L '' S := by
      change L' '' (Q '' S) = L '' S
      rw [image_image]
      congr 1
      funext a
      exact hfactor a
    rw [← himage]
    exact ih hcompactT L' y hfiniteT hlocalT

theorem compact_finite_linear_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set E} (hS : IsCompact S) (L : E →L[ℂ] F) (y : F)
    (hfinite : {v | v ∈ S ∧ L v = y}.Finite)
    (hlocal : ∀ v ∈ S, L v = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  let e := (Module.finBasis ℂ E).equivFunL
  let T := e '' S
  let L' := L.comp e.symm.toContinuousLinearMap
  have hfiniteT : {a | a ∈ T ∧ L' a = y}.Finite := by
    apply (hfinite.image e).subset
    rintro a ⟨⟨v, hv, rfl⟩, ha⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    simpa only [L', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using ha
  have hlocalT : ∀ a ∈ T, L' a = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T a := by
    rintro a ⟨v, hv, rfl⟩ ha
    apply (hlocal v hv ?_).image_equiv e
    simpa only [L', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using ha
  have h := compact_finite_linear_image_coordinates (Module.finrank ℂ E) (hS.image e.continuous)
    L' y hfiniteT hlocalT
  have heq : L' '' T = L '' S := by
    simp only [T, L', image_image, ContinuousLinearMap.coe_comp, Function.comp_def,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
  rwa [heq] at h

end

section

/-! Compact pieces of holomorphic graphs give local equations for their
finite images at fibers contained in the interior of the piece. -/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization.Constructions.Cone

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
theorem compact_graph_local_equations {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U)
    (hxK : K ∈ 𝓝 x) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((fun z => (z, f z)) '' K) (x, f x) := by
  have hd : DifferentiableOn ℂ (fun p : E × F => p.2 - f p.1) (Prod.fst ⁻¹' U) :=
    differentiable_snd.differentiableOn.sub
      (hf.comp differentiable_fst.differentiableOn (fun _ hz => hz))
  have h := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticSetOperations.Constructions.Cone.holomorphicZeroSetAt_zero_fiber (hU.preimage continuous_fst) hd (show (x, f x) ∈ Prod.fst ⁻¹' U from hx)
  apply h.congr
  filter_upwards [continuous_fst.continuousAt.eventually hxK] with p hp
  constructor
  · rintro ⟨z, _, rfl⟩
    exact sub_self _
  · intro hz
    exact ⟨p.1, hp, Prod.ext rfl (sub_eq_zero.mp hz).symm⟩

theorem compact_holomorphic_image_local {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (y : F) (hfinite : {z | z ∈ K ∧ f z = y}.Finite)
    (hinterior : ∀ z ∈ K, f z = y → K ∈ 𝓝 z) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' K) y := by
  let S := (fun z => (z, f z)) '' K
  have hS : IsCompact S := hK.image_of_continuousOn
    (continuousOn_id.prodMk (hf.continuousOn.mono hKU))
  let L : E × F →L[ℂ] F := ContinuousLinearMap.snd ℂ E F
  have hfin : {p | p ∈ S ∧ L p = y}.Finite := by
    apply (hfinite.image (fun z => (z, f z))).subset
    rintro p ⟨⟨z, hz, rfl⟩, hp⟩
    exact ⟨z, ⟨hz, hp⟩, rfl⟩
  have hloc : ∀ p ∈ S, L p = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S p := by
    rintro p ⟨z, hz, rfl⟩ hp
    exact compact_graph_local_equations hU hf (hKU hz) (hinterior z hz hp)
  have heq : L '' S = f '' K := by
    change Prod.snd '' ((fun z => (z, f z)) '' K) = f '' K
    rw [image_image]
  rw [← heq]
  exact compact_finite_linear_image hS L y hfin hloc

theorem compact_injective_holomorphic_image_local {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hinj : InjOn f K) {x : E} (hx : x ∈ K) (hxK : K ∈ 𝓝 x) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' K) (f x) := by
  apply compact_holomorphic_image_local hU hf hK hKU (f x)
  · have hsub : ({z | z ∈ K ∧ f z = f x} : Set E).Subsingleton :=
      fun _ hz _ hw => hinj hz.1 hw.1 (hz.2.trans hw.2.symm)
    exact hsub.finite
  · intro z hz hzx
    simpa only [hinj hz hx hzx] using hxK

end

/-! Locally analytic subsets of a compact holomorphic graph have analytic
images at finite fibers, with no condition on remote boundary points. -/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization.Constructions.Cone

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
theorem analytic_graph_local_equations {f : E → F} {U S : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U)
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((fun z => (z, f z)) '' S) (x, f x) := by
  have hgraph := compact_graph_local_equations hU hf hx (K := univ) Filter.univ_mem
  have hpre := hS.preimage (g := Prod.fst) isOpen_univ (mem_univ (x, f x)) differentiable_fst.differentiableOn
  have heq : (fun z => (z, f z)) '' S =
      ((fun z => (z, f z)) '' univ) ∩ Prod.fst ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, mem_univ _, rfl⟩, hz⟩
    · rintro ⟨⟨z, _, rfl⟩, hz⟩
      exact ⟨z, hz, rfl⟩
  rw [heq]
  exact hgraph.inter hpre

theorem compact_holomorphic_analytic_image_local {f : E → F} {U S : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hS : IsCompact S) (hSU : S ⊆ U)
    (y : F) (hfinite : {z | z ∈ S ∧ f z = y}.Finite)
    (hlocal : ∀ z ∈ S, f z = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S z) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' S) y := by
  let T := (fun z => (z, f z)) '' S
  have hT : IsCompact T := hS.image_of_continuousOn
    (continuousOn_id.prodMk (hf.continuousOn.mono hSU))
  let L : E × F →L[ℂ] F := ContinuousLinearMap.snd ℂ E F
  have hfin : {p | p ∈ T ∧ L p = y}.Finite := by
    apply (hfinite.image (fun z => (z, f z))).subset
    rintro p ⟨⟨z, hz, rfl⟩, hp⟩
    exact ⟨z, ⟨hz, hp⟩, rfl⟩
  have hloc : ∀ p ∈ T, L p = y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T p := by
    rintro p ⟨z, hz, rfl⟩ hp
    exact analytic_graph_local_equations hU hf (hSU hz) (hlocal z hz hp)
  have heq : L '' T = f '' S := by
    change Prod.snd '' ((fun z => (z, f z)) '' S) = f '' S
    rw [image_image]
  rw [← heq]
  exact compact_finite_linear_image hT L y hfin hloc

end

end OAI.RepresentationTheory.Theta.Geometric.CompactAnalyticImage
