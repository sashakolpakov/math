import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Algebra.Module.Equiv

/-! # Complex Normal Block -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock.Cycles

noncomputable section

/-!
# The normal block of a tangent-preserving complex linear equivalence

If an ambient continuous linear equivalence and its inverse preserve the
horizontal subspace, its second coordinate descends to a continuous linear
equivalence of the normal factors. No finite-dimensionality or completeness
assumption is needed. The resulting map agrees with the existing construction
of the induced map on the actual quotient by the tangent subspace.
-/

universe uE uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The bottom-right continuous linear block of an ambient equivalence. -/
def normalBlockMap (L : (E × F) ≃L[ℂ] (E × F)) : F →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp
    (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ E F))

@[simp]
theorem normalBlockMap_apply (L : (E × F) ≃L[ℂ] (E × F)) (y : F) :
    normalBlockMap L y = (L (0, y)).2 :=
  rfl

/-- Preservation of the horizontal subspace makes the second coordinate
depend only on the normal coordinate. -/
theorem normalBlockMap_projection (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (z : E × F) :
    (L z).2 = normalBlockMap L z.2 := by
  have h := congrArg Prod.snd
    (ContinuousLinearMap.comp_inl_add_comp_inr L.toContinuousLinearMap z)
  change (L (z.1, 0)).2 + (L (0, z.2)).2 = (L z).2 at h
  rw [hL z.1, zero_add] at h
  exact h.symm

/-- The normal block is invertible because the ambient equivalence and its
inverse both preserve the horizontal subspace. Its inverse is the normal
block of the ambient inverse. -/
def normalBlock (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) : F ≃L[ℂ] F where
  toFun := normalBlockMap L
  invFun := normalBlockMap L.symm
  left_inv y := by
    change normalBlockMap L.symm (L (0, y)).2 = y
    rw [← normalBlockMap_projection L.symm hLi (L (0, y))]
    exact congrArg Prod.snd (L.symm_apply_apply (0, y))
  right_inv y := by
    change normalBlockMap L (L.symm (0, y)).2 = y
    rw [← normalBlockMap_projection L hL (L.symm (0, y))]
    exact congrArg Prod.snd (L.apply_symm_apply (0, y))
  map_add' := (normalBlockMap L).map_add
  map_smul' := (normalBlockMap L).map_smul
  continuous_toFun := (normalBlockMap L).continuous
  continuous_invFun := (normalBlockMap L.symm).continuous

@[simp]
theorem normalBlock_apply (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) (y : F) :
    normalBlock L hL hLi y = (L (0, y)).2 :=
  rfl

@[simp]
theorem normalBlock_symm_apply (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) (y : F) :
    (normalBlock L hL hLi).symm y = (L.symm (0, y)).2 :=
  rfl

@[simp]
theorem normalBlock_toContinuousLinearMap (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (normalBlock L hL hLi).toContinuousLinearMap =
      (ContinuousLinearMap.snd ℂ E F).comp
        (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ E F)) :=
  rfl

theorem normalBlock_projection (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) (z : E × F) :
    (L z).2 = normalBlock L hL hLi z.2 :=
  normalBlockMap_projection L hL z

/-- The second projection intertwines the ambient and normal equivalences. -/
theorem normalBlock_comp_snd (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (normalBlock L hL hLi).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ E F) =
      (ContinuousLinearMap.snd ℂ E F).comp L.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  exact (normalBlock_projection L hL hLi z).symm

@[simp]
theorem normalBlock_symm (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (normalBlock L hL hLi).symm = normalBlock L.symm hLi hL := by
  ext y
  rfl

/-- The two preservation hypotheses give exactly the submodule equality
required by the existing induced normal-quotient equivalence. -/
theorem normalBlock_tangent_map (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0) :
    (LinearMap.ker (LinearMap.snd ℂ E F)).map L.toLinearEquiv.toLinearMap =
      LinearMap.ker (LinearMap.snd ℂ E F) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (L w).2 = 0
    rw [normalBlockMap_projection L hL w]
    change w.2 = 0 at hw
    rw [hw, map_zero]
  · intro hz
    refine ⟨L.symm z, ?_, L.apply_symm_apply z⟩
    change (L.symm z).2 = 0
    rw [normalBlockMap_projection L.symm hLi z]
    change z.2 = 0 at hz
    rw [hz, map_zero]

/-- Under the native quotient identification with the normal factor, the
existing induced quotient equivalence is exactly the normal block. -/
theorem normalBlock_quotient (L : (E × F) ≃L[ℂ] (E × F))
    (hL : ∀ x : E, (L (x, 0)).2 = 0)
    (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (z : ComplexNormalEq.Cycles.ComplexNormal (LinearMap.ker (LinearMap.snd ℂ E F))) :
    let e := (LinearMap.snd ℂ E F).quotKerEquivOfSurjective
      (fun y => ⟨(0, y), rfl⟩)
    e (ComplexNormalEq.Cycles.complexNormalEquiv _ _ L.toLinearEquiv (normalBlock_tangent_map L hL hLi) z) =
      normalBlock L hL hLi (e z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z => exact normalBlock_projection L hL hLi z

/-- The generic quotient comparison specializes to the existing displayed
coordinate-normal equivalence without changing its definition. -/
theorem normalBlock_coordinateNormalEquiv (n p : ℕ)
    (L : ((Fin n → ℂ) × (Fin p → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin p → ℂ)))
    (hL : ∀ x : Fin n → ℂ, (L (x, 0)).2 = 0)
    (hLi : ∀ x : Fin n → ℂ, (L.symm (x, 0)).2 = 0)
    (z : ComplexNormalEq.Cycles.ComplexNormal (ComplexNormalEq.Cycles.coordinateTangent n p)) :
    ComplexNormalEq.Cycles.coordinateNormalEquiv n p
        (ComplexNormalEq.Cycles.complexNormalEquiv _ _ L.toLinearEquiv (normalBlock_tangent_map L hL hLi) z) =
      normalBlock L hL hLi (ComplexNormalEq.Cycles.coordinateNormalEquiv n p z) :=
  normalBlock_quotient L hL hLi z

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalBlock.Cycles
