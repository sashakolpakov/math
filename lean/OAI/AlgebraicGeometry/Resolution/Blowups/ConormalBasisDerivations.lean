import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ConormalDerivationLift
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Conormal Basis Derivations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ConormalBasisDerivations.Construction

noncomputable section

section

/-! Conormal generators lift to generators of the original center on a principal neighborhood. -/

variable {R ι : Type*} [CommRing R]

theorem conormal_generators_span_mod_square (I : Ideal R) (g : ι → I)
    (h : Submodule.span R (Set.range (fun i => I.toCotangent (g i))) = ⊤) :
    I = Ideal.span (Set.range (fun i => (g i).val)) ⊔ I ^ 2 := by
  let N := Submodule.span R (Set.range g)
  have hm : N.map I.toCotangent = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h
  have he : N ⊔ LinearMap.ker I.toCotangent = ⊤ := by
    have hc := congrArg (Submodule.comap I.toCotangent) hm
    rwa [Submodule.comap_map_eq, Submodule.comap_top] at hc
  have hc := congrArg (Submodule.map I.subtype) he
  rw [Submodule.map_sup, I.map_toCotangent_ker, Submodule.map_top, I.range_subtype] at hc
  change (Submodule.span R (Set.range g)).map I.subtype ⊔ I ^ 2 = I at hc
  rw [Submodule.map_span, ← Set.range_comp] at hc
  exact hc.symm

open scoped Pointwise in
theorem exists_center_generator_principal_neighborhood
    (I G : Ideal R) (hfg : I.FG) (hGI : G ≤ I) (hgen : I ≤ G ⊔ I ^ 2) :
    ∃ r : R, r - 1 ∈ I ∧
      I.map (algebraMap R (Localization.Away r)) = G.map (algebraMap R (Localization.Away r)) := by
  have hs : I ≤ G ⊔ I • I := by simpa only [smul_eq_mul, pow_two] using hgen
  obtain ⟨r, hr, hRI⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hs
  refine ⟨r, hr, le_antisymm ?_ (Ideal.map_mono hGI)⟩
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hprod : r * x ∈ G := hRI (Submodule.smul_mem_pointwise_smul x r I hx)
  let S := Localization.Away r
  let f := algebraMap R S
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (R := R) (S := S) r
  have hm : f r * f x ∈ G.map f := by simpa only [map_mul] using Ideal.mem_map_of_mem f hprod
  have hn := (G.map f).mul_mem_left (↑u⁻¹ : S) hm
  rw [← hu, ← mul_assoc, Units.inv_mul, one_mul] at hn
  exact hn

theorem generator_neighborhood_avoids_center_prime
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) (r : R) (hr : r - 1 ∈ I) : r ∉ p := by
  intro hp
  have h1 := p.sub_mem hp (hIp hr)
  have he : r - (r - 1) = 1 := by ring
  rw [he] at h1
  exact (inferInstance : p.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

end

/-! A conormal basis gives actual center generators modulo squares and ambient dual derivations modulo the center. -/

theorem span_eq_top_restrict_scalars_of_surjective
    {R Q M ι : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    [AddCommGroup M] [Module R M] [Module Q M] [IsScalarTower R Q M]
    (hq : Function.Surjective (algebraMap R Q)) (v : ι → M)
    (h : Submodule.span Q (Set.range v) = ⊤) : Submodule.span R (Set.range v) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hx : x ∈ Submodule.span Q (Set.range v) := h.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      obtain ⟨r, rfl⟩ := hq c
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ r hx

theorem exists_extension_derivation_of_conormal_functional
    {k Q : Type*} [CommRing k] [CommRing Q] [Algebra k Q]
    (P : Algebra.Extension k Q) [Algebra.FormallySmooth k P.Ring] [Algebra.FormallySmooth k Q]
    (L : P.Cotangent →ₗ[Q] Q) :
    ∃ E : Derivation k P.Ring P.Ring, ∀ x : P.ker,
      algebraMap P.Ring Q (E x.val) = L (Algebra.Extension.Cotangent.mk x) := by
  let L' : P.ker.Cotangent →ₗ[P.Ring] Q :=
    (L.restrictScalars P.Ring).comp P.cotangentEquivCotangentKer.symm.toLinearMap
  obtain ⟨E, hE⟩ := Smooth.ConormalDerivationLift.Construction.exists_ambient_derivation_of_conormal_functional k P.algebraMap_surjective L'
  exact ⟨E, hE⟩

theorem exists_conormal_basis_generators_and_derivations
    {k Q ι : Type*} [CommRing k] [CommRing Q] [Algebra k Q] [DecidableEq ι]
    (P : Algebra.Extension k Q) [Algebra.FormallySmooth k P.Ring] [Algebra.FormallySmooth k Q]
    (b : Module.Basis ι Q P.Cotangent) :
    ∃ (g : ι → P.ker) (E : ι → Derivation k P.Ring P.Ring),
      P.ker = Ideal.span (Set.range (fun i => (g i).val)) ⊔ P.ker ^ 2 ∧
      ∀ i j, algebraMap P.Ring Q (E i (g j).val) = if i = j then 1 else 0 := by
  classical
  choose g hg using fun i => Algebra.Extension.Cotangent.mk_surjective (P := P) (b i)
  choose E hE using fun i => exists_extension_derivation_of_conormal_functional P (b.coord i)
  have hspan : Submodule.span P.Ring (Set.range (fun i => Algebra.Extension.Cotangent.mk (g i))) = ⊤ := by
    apply span_eq_top_restrict_scalars_of_surjective P.algebraMap_surjective
    have hv : (fun i => Algebra.Extension.Cotangent.mk (g i)) = b := funext hg
    rw [hv, b.span_eq]
  have hspan' : Submodule.span P.Ring (Set.range (fun i => P.ker.toCotangent (g i))) = ⊤ := by
    have h := congrArg (Submodule.map P.cotangentEquivCotangentKer.toLinearMap) hspan
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr P.cotangentEquivCotangentKer.surjective] at h
    exact h
  refine ⟨g, E, conormal_generators_span_mod_square P.ker g hspan', ?_⟩
  intro i j
  rw [hE, hg]
  simpa only [Module.Basis.coord_apply, eq_comm] using b.repr_self_apply j i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ConormalBasisDerivations.Construction
