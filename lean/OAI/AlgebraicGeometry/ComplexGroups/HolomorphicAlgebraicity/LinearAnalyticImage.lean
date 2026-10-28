import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperAnalyticImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection

/-! # Linear Analytic Image -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage

noncomputable section

/-!
# Analytic images under linear projections with one-dimensional kernels

Linear coordinates turn a projection along a normalized vector into a
coordinate projection. This transports the proper finite projection theorem
to the concrete projections used for the projective graph cone.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

namespace Constructions.Cone

theorem holomorphicZeroSetAt_linear_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (e : E ≃L[ℂ] ((Fin n → ℂ) × ℂ)) {S : Set E} {x : Fin n → ℂ}
    (hproper : IsProperMap (fun p : S => (e p.val).1))
    (hfinite : {v : E | v ∈ S ∧ (e v).1 = x}.Finite)
    (hlocal : ∀ v ∈ S, (e v).1 = x → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((fun v => (e v).1) '' S) x := by
  let T := e.symm ⁻¹' S
  let h : T ≃ₜ S := e.symm.toHomeomorph.subtype (fun _ => Iff.rfl)
  have hproperT : IsProperMap (fun p : T => p.val.1) := by
    convert hproper.comp h.isProperMap using 1
    funext p
    exact (congrArg Prod.fst (e.apply_symm_apply p.val)).symm
  have hfiniteT : {z : ℂ | (x, z) ∈ T}.Finite := by
    have hinj : Function.Injective (fun z : ℂ => e.symm (x, z)) := by
      intro a b hab
      exact congrArg Prod.snd (e.symm.injective hab)
    have ht := hfinite.preimage hinj.injOn
    convert ht using 1
    ext z
    simp only [T, mem_preimage, mem_ofPred_eq, e.apply_symm_apply, and_true]
  have hlocalT : ∀ z, (x, z) ∈ T → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T (x, z) := by
    intro z hz
    apply (hlocal (e.symm (x, z)) hz (by simp)).preimage isOpen_univ (mem_univ _)
      e.symm.differentiable.differentiableOn
  have himage := ProperAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_proper_projection hproperT hfiniteT hlocalT
  apply himage.congr
  apply Filter.Eventually.of_forall
  intro y
  constructor
  · rintro ⟨v, hv, hvy⟩
    refine ⟨(e v).2, ?_⟩
    change e.symm (y, (e v).2) ∈ S
    rw [← hvy]
    simpa only [Prod.eta, e.symm_apply_apply] using hv
  · rintro ⟨z, hz⟩
    exact ⟨e.symm (y, z), hz, by simp⟩

end Constructions.Cone

namespace Constructions.Segre

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def projectionAlongEquiv (i : ι) (w : ι → ℂ) :
    (ι → ℂ) ≃L[ℂ] (({j : ι // j ≠ i} → ℂ) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun v => (SegreProjection.Constructions.Segre.projectionAlong i w v, v i)
    invFun := fun p j => if h : j = i then p.2 else p.1 ⟨j, h⟩ + p.2 * w j
    left_inv := by
      intro v
      ext j
      by_cases hj : j = i
      · simp [hj]
      · simp [hj, SegreProjection.Constructions.Segre.projectionAlong]
    right_inv := by
      intro p
      apply Prod.ext
      · ext j
        simp [SegreProjection.Constructions.Segre.projectionAlong, j.property]
      · simp
    map_add' := by intro v u; exact Prod.ext (map_add _ _ _) rfl
    map_smul' := by intro a v; exact Prod.ext (map_smul _ _ _) rfl }

theorem projectionAlongEquiv_fst (i : ι) (w : ι → ℂ) (v : ι → ℂ) :
    (projectionAlongEquiv i w v).1 = SegreProjection.Constructions.Segre.projectionAlong i w v := rfl

/-- The concrete projection of a closed cone is locally analytic away from
zero whenever its center avoids the cone and the cone is analytic off zero. -/
theorem holomorphicZeroSetAt_projectionAlong {S : Set (ι → ℂ)}
    (hS : IsClosed S) (hcone : ∀ (c : ℂ) ⦃v : ι → ℂ⦄, v ∈ S → c • v ∈ S)
    (i : ι) (w : ι → ℂ) (hw : w i = 1) (hwS : w ∉ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (y : {j : ι // j ≠ i} → ℂ) (hy : y ≠ 0) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (SegreProjection.Constructions.Segre.projectionAlong i w '' S) y := by
  let F := {j : ι // j ≠ i} → ℂ
  let b := (Module.finBasis ℂ F).equivFunL
  let e := (projectionAlongEquiv i w).trans
    (b.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ))
  have he (v : ι → ℂ) : (e v).1 = b (SegreProjection.Constructions.Segre.projectionAlong i w v) := rfl
  have hproper : IsProperMap (fun v : S => (e v.val).1) :=
    b.toHomeomorph.isProperMap.comp (SegreProjection.Constructions.Segre.isProperMap_projectionAlong hS hcone i w hw hwS)
  have hfinite : {v : ι → ℂ | v ∈ S ∧ (e v).1 = b y}.Finite := by
    have h := SegreProjection.Constructions.Segre.finite_projectionAlong_fiber hS hcone i w hw hwS hlocal y
    simpa only [he, b.injective.eq_iff] using h
  have hloc : ∀ v ∈ S, (e v).1 = b y → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v := by
    intro v hv hvy
    apply hlocal v hv
    intro hv0
    have hLy : SegreProjection.Constructions.Segre.projectionAlong i w v = y := b.injective hvy
    rw [hv0, map_zero] at hLy
    exact hy hLy.symm
  have himage := Cone.holomorphicZeroSetAt_linear_projection e hproper hfinite hloc
  have hpull := himage.preimage (g := b) isOpen_univ (mem_univ y)
    b.differentiable.differentiableOn
  apply hpull.congr
  apply Filter.Eventually.of_forall
  intro z
  change z ∈ SegreProjection.Constructions.Segre.projectionAlong i w '' S ↔ b z ∈ (fun v => (e v).1) '' S
  constructor
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, congrArg b hvz⟩
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, b.injective hvz⟩

end Constructions.Segre

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage
