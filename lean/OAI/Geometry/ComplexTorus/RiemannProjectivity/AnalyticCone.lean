import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage
import Mathlib.Analysis.Normed.Module.Complemented

/-! # Analytic Cone -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone.Constructions.AnalyticConeImage

noncomputable section

/-!
# RiemannProjectivity: analytic images after eliminating several cone coordinates

Successive one-coordinate projections preserve closedness, the cone property,
and the absence of a nonzero kernel point. Proper analytic elimination can
therefore be iterated through an arbitrary finite-dimensional kernel.
-/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage.Constructions.Cone

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem one_coordinate (e : V ≃L[ℂ] (W × ℂ)) {S : Set V}
    (hS : IsClosed S) (hcone : ∀ (c : ℂ) ⦃v : V⦄, v ∈ S → c • v ∈ S)
    (hkernel : ∀ v ∈ S, (e v).1 = 0 → v = 0)
    (hlocal : ∀ v ∈ S, v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (y : W) (hy : y ≠ 0) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((fun v => (e v).1) '' S) y := by
  let P := (ContinuousLinearMap.fst ℂ W ℂ).comp e.toContinuousLinearMap
  let b := (Module.finBasis ℂ W).equivFunL
  let e' := e.trans (b.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ))
  have hproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hS hcone P hkernel
  have hp : IsProperMap (fun v : S => (e' v.val).1) :=
    b.toHomeomorph.isProperMap.comp hproper
  have hf : {v : V | v ∈ S ∧ (e' v).1 = b y}.Finite := by
    have h := FiniteCone.Constructions.FiniteConeFibers.finite_proper_cone_fiber P hproper hkernel hlocal y
    change {v : V | v ∈ S ∧ (e v).1 = y}.Finite at h
    simpa only [e', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      b.injective.eq_iff] using h
  have hl : ∀ v ∈ S, (e' v).1 = b y → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v := by
    intro v hv hvy
    apply hlocal v hv
    intro hz
    have h : (e v).1 = y := b.injective hvy
    exact hy (by simpa only [hz, map_zero, Prod.fst_zero] using h.symm)
  have h := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_linear_projection e' hp hf hl
  have hpull := h.preimage (g := b) isOpen_univ (mem_univ y) b.differentiable.differentiableOn
  apply hpull.congr
  apply Filter.Eventually.of_forall
  intro z
  change z ∈ (fun v => (e v).1) '' S ↔ b z ∈ (fun v => b (e v).1) '' S
  constructor
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, congrArg b hvz⟩
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, b.injective hvz⟩

def splitCoordinate (n : ℕ) :
    (W × (Fin (n + 1) → ℂ)) ≃L[ℂ] ((W × (Fin n → ℂ)) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p => ((p.1, Fin.tail p.2), p.2 0)
    invFun := fun p => (p.1.1, Fin.cons p.2 p.1.2)
    left_inv := by intro p; ext i <;> simp
    right_inv := by intro p; ext i <;> simp
    map_add' := by intro p q; rfl
    map_smul' := by intro c p; rfl }

theorem product_projection (n : ℕ) {S : Set (W × (Fin n → ℂ))}
    (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v : W × (Fin n → ℂ)⦄, v ∈ S → c • v ∈ S)
    (hkernel : ∀ v ∈ S, v.1 = 0 → v = 0)
    (hlocal : ∀ v ∈ S, v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (y : W) (hyS : y ∈ Prod.fst '' S) (hy : y ≠ 0) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (Prod.fst '' S) y := by
  induction n with
  | zero =>
    have heq : (fun w : W => (w, (0 : Fin 0 → ℂ))) ⁻¹' S = Prod.fst '' S := by
      ext w
      constructor
      · intro hw
        exact ⟨(w, 0), hw, rfl⟩
      · rintro ⟨⟨u, a⟩, hp, rfl⟩
        change (u, 0) ∈ S
        simpa only [Subsingleton.elim a 0] using hp
    have hyp : (y, (0 : Fin 0 → ℂ)) ∈ S := by
      change y ∈ (fun w : W => (w, (0 : Fin 0 → ℂ))) ⁻¹' S
      rwa [heq]
    have hn : (y, (0 : Fin 0 → ℂ)) ≠ 0 := fun h => hy (congrArg Prod.fst h)
    have h := (hlocal (y, 0) hyp hn).preimage (g := fun w : W => (w, (0 : Fin 0 → ℂ)))
      isOpen_univ (mem_univ y)
      (differentiable_id.prodMk (differentiable_const (0 : Fin 0 → ℂ))).differentiableOn
    rwa [heq] at h
  | succ n ih =>
    let e := splitCoordinate (W := W) n
    let P := (ContinuousLinearMap.fst ℂ (W × (Fin n → ℂ)) ℂ).comp e.toContinuousLinearMap
    let T := P '' S
    have hPfirst (v : W × (Fin (n + 1) → ℂ)) : (P v).1 = v.1 := rfl
    have hPkernel : ∀ v ∈ S, P v = 0 → v = 0 := by
      intro v hv hp
      exact hkernel v hv (congrArg Prod.fst hp)
    have hproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hS hcone P hPkernel
    have hT : IsClosed T := by
      have h := hproper.isClosedMap.isClosed_range
      convert! h using 1
      ext u
      exact ⟨fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩,
        fun ⟨v, he⟩ => ⟨v, v.property, he⟩⟩
    have hTcone : ∀ (c : ℂ) ⦃v : W × (Fin n → ℂ)⦄, v ∈ T → c • v ∈ T := by
      rintro c v ⟨w, hw, rfl⟩
      exact ⟨c • w, hcone c hw, map_smul P c w⟩
    have hTkernel : ∀ v ∈ T, v.1 = 0 → v = 0 := by
      rintro v ⟨w, hw, rfl⟩ hv
      rw [hkernel w hw hv, map_zero]
    have hTlocal : ∀ v ∈ T, v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T v :=
      fun v _ hv => one_coordinate e hS hcone hPkernel hlocal v hv
    have heq : Prod.fst '' T = Prod.fst '' S := by
      change Prod.fst '' (P '' S) = Prod.fst '' S
      rw [image_image]
      rfl
    have hyn : y ∈ Prod.fst '' T := heq ▸ hyS
    have h := ih hT hTcone hTkernel hTlocal hyn
    rwa [heq] at h

theorem projection_coordinates (L : V →L[ℂ] W) (hL : Function.Surjective L) :
    ∃ (k : ℕ) (e : V ≃L[ℂ] (W × (Fin k → ℂ))), ∀ v, (e v).1 = L v := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  let hk := L.ker_closedComplemented_of_finiteDimensional_range
  let g := Classical.choose hk
  let e₀ := L.equivProdOfSurjectiveOfIsCompl g (LinearMap.range_eq_top.mpr hL)
    (LinearMap.range_eq_of_proj (Classical.choose_spec hk))
    (LinearMap.isCompl_of_proj (Classical.choose_spec hk))
  let b := (Module.finBasis ℂ L.ker).equivFunL
  exact ⟨Module.finrank ℂ L.ker,
    e₀.trans ((ContinuousLinearEquiv.refl ℂ W).prodCongr b), fun _ => rfl⟩

theorem linear_projection (L : V →L[ℂ] W) (hL : Function.Surjective L)
    {S : Set V} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v : V⦄, v ∈ S → c • v ∈ S)
    (hkernel : ∀ v ∈ S, L v = 0 → v = 0)
    (hlocal : ∀ v ∈ S, v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (y : W) (hyS : y ∈ L '' S) (hy : y ≠ 0) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  obtain ⟨k, e, he⟩ := projection_coordinates L hL
  let T := e.symm ⁻¹' S
  have hT : IsClosed T := hS.preimage e.symm.continuous
  have hTcone : ∀ (c : ℂ) ⦃v : W × (Fin k → ℂ)⦄, v ∈ T → c • v ∈ T := by
    intro c v hv
    change e.symm (c • v) ∈ S
    rw [map_smul]
    exact hcone c hv
  have hTkernel : ∀ v ∈ T, v.1 = 0 → v = 0 := by
    intro v hv hv0
    apply e.symm.injective
    rw [map_zero]
    apply hkernel _ hv
    rw [← he, e.apply_symm_apply, hv0]
  have hTlocal : ∀ v ∈ T, v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T v := by
    intro v hv hv0
    have hn : e.symm v ≠ 0 := fun h => hv0 (e.symm.injective (h.trans (map_zero _).symm))
    exact (hlocal _ hv hn).preimage isOpen_univ (mem_univ v) e.symm.differentiable.differentiableOn
  have himage : Prod.fst '' T = L '' S := by
    ext w
    constructor
    · rintro ⟨v, hv, hvw⟩
      exact ⟨e.symm v, hv, by rw [← he, e.apply_symm_apply, hvw]⟩
    · rintro ⟨v, hv, hvw⟩
      exact ⟨e v, by simpa only [T, mem_preimage, e.symm_apply_apply] using hv,
        (he v).trans hvw⟩
  have hymem : y ∈ Prod.fst '' T := himage ▸ hyS
  have h := product_projection k hT hTcone hTkernel hTlocal y hymem hy
  rwa [himage] at h

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone.Constructions.AnalyticConeImage
