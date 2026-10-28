import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicRegularity
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement

/-! # Immersion -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Immersion

noncomputable section

/-!
# Holomorphic normal charts from injective derivatives

Adjoining complementary linear directions turns an injective derivative into
an invertible derivative. The checked holomorphic inverse theorem then gives
actual local normal coordinates.
-/

open Set
open scoped _root_.Topology

namespace Constructions.Regularity

/-- An injective derivative supplies a holomorphic chart on the ambient
space whose zero slice is the given map. -/
theorem exists_holomorphic_normal_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) (hinj : Function.Injective (fderiv ℂ f x)) :
    ∃ (C : Submodule ℂ F) (q : OpenPartialHomeomorph (E × C) F),
      (x, 0) ∈ q.source ∧
      (∀ z, q z = f z.1 + (z.2 : F)) ∧
      DifferentiableOn ℂ q q.source ∧ DifferentiableOn ℂ q.symm q.target := by
  obtain ⟨C, e, he⟩ := ComplexPoints.Analytic.LinearImmersionComplement.exists_linearImmersionComplement
    (fderiv ℂ f x) hinj
  let g : E × C → F := fun z => f z.1 + (z.2 : F)
  have hfst : Differentiable ℂ (Prod.fst : E × C → E) := differentiable_fst
  have hsnd : Differentiable ℂ (Prod.snd : E × C → C) := differentiable_snd
  have hg : DifferentiableOn ℂ g (Prod.fst ⁻¹' U) :=
    (hf.comp hfst.differentiableOn (mapsTo_preimage Prod.fst U)).add
      (C.subtypeL.differentiable.comp hsnd).differentiableOn
  have hderiv : HasFDerivAt g
      ((fderiv ℂ f x).comp (ContinuousLinearMap.fst ℂ E C) +
        C.subtypeL.comp (ContinuousLinearMap.snd ℂ E C)) (x, 0) := by
    exact ((hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt.comp
      (x, 0) hasFDerivAt_fst).add
        (C.subtypeL.hasFDerivAt.comp (x, 0) hasFDerivAt_snd)
  have heq : (fderiv ℂ f x).comp (ContinuousLinearMap.fst ℂ E C) +
      C.subtypeL.comp (ContinuousLinearMap.snd ℂ E C) = e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    exact (he z).symm
  rw [heq] at hderiv
  obtain ⟨q, hxq, hqg, hq, hqi⟩ := HolomorphicRegularity.Constructions.Regularity.exists_holomorphic_localInverse
    (hU.preimage continuous_fst) hg hx e hderiv.fderiv
  exact ⟨C, q, hxq, fun z => congrFun hqg z, hq, hqi⟩

end Constructions.Regularity

namespace Constructions.Cone

/-- A holomorphic map to a finite-dimensional complex space gives finitely
many scalar holomorphic equations for its zero locus. -/
theorem holomorphicZeroSetAt_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {z | f z = 0} x := by
  let e := (Module.finBasis ℂ F).equivFunL
  refine ⟨U, hU, hx, Module.finrank ℂ F, (fun i z => e (f z) i), (fun i => ?_), ?_⟩
  · have heval : Differentiable ℂ
        (fun z : Fin (Module.finrank ℂ F) → ℂ => z i) := differentiable_apply i
    exact heval.comp_differentiableOn (e.differentiable.comp_differentiableOn hf)
  · intro z _
    constructor
    · intro hz i
      simp only [mem_ofPred_eq] at hz
      simp only [hz, map_zero, Pi.zero_apply]
    · intro hz
      change f z = 0
      apply e.injective
      ext i
      simpa only [map_zero, Pi.zero_apply] using hz i

/-- A holomorphic embedding of an open finite-dimensional coordinate domain
has a locally holomorphic image. The normal equations are constructed from
the inverse normal chart and its complementary coordinates. -/
theorem holomorphicZeroSetAt_image_of_embedding
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hemb : Topology.IsEmbedding (fun z : U => f z)) {x : E} (hx : x ∈ U)
    (hinj : Function.Injective (fderiv ℂ f x)) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' U) (f x) := by
  obtain ⟨C, q, hxq, hqmap, _, hqi⟩ :=
    Regularity.exists_holomorphic_normal_chart hU hf hx hinj
  have hxqf : q (x, 0) = f x := by simpa only [ZeroMemClass.coe_zero, add_zero] using hqmap (x, 0)
  have hxT : f x ∈ q.target := hxqf ▸ q.map_source hxq
  have hxinv : q.symm (f x) = (x, 0) := by
    rw [← hxqf]
    exact q.left_inv hxq
  let W : Set U := {z | (z.val, (0 : C)) ∈ q.source}
  have hW : IsOpen W := q.open_source.preimage
    (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨O, hO, hOp⟩ := hemb.isInducing.isOpen_iff.mp hW
  have hxO : f x ∈ O := by
    change (⟨x, hx⟩ : U) ∈ (fun z : U => f z) ⁻¹' O
    rw [hOp]
    exact hxq
  let V : Set F := (q.target ∩ q.symm ⁻¹' (Prod.fst ⁻¹' U)) ∩ O
  have hV : IsOpen V :=
    (hqi.continuousOn.isOpen_inter_preimage q.open_target
      (hU.preimage continuous_fst)).inter hO
  have hxV : f x ∈ V := ⟨⟨hxT, by simpa only [mem_preimage, hxinv] using hx⟩, hxO⟩
  have hsnd : Differentiable ℂ (Prod.snd : E × C → C) := differentiable_snd
  have hzero := holomorphicZeroSetAt_zero q.open_target
    (hsnd.comp_differentiableOn hqi) hxT
  apply hzero.congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  constructor
  · rintro ⟨z, hzU, hzy⟩
    have hzW : (z, (0 : C)) ∈ q.source := by
      change (⟨z, hzU⟩ : U) ∈ W
      rw [← hOp]
      change f z ∈ O
      rw [hzy]
      exact hy.2
    have hqzy : q (z, 0) = y := by
      simpa only [ZeroMemClass.coe_zero, add_zero, hzy] using hqmap (z, 0)
    have hinvy : q.symm y = (z, 0) := by
      rw [← hqzy]
      exact q.left_inv hzW
    change (q.symm y).2 = 0
    rw [hinvy]
  · intro hz
    change (q.symm y).2 = 0 at hz
    refine ⟨(q.symm y).1, hy.1.2, ?_⟩
    have heq := q.right_inv hy.1.1
    rw [hqmap, hz] at heq
    simpa only [ZeroMemClass.coe_zero, add_zero] using heq

end Constructions.Cone

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Immersion
