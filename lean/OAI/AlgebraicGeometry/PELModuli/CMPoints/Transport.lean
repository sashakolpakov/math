import OAI.AlgebraicGeometry.PELModuli.CMPoints.Realization

/-! # Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Transport

noncomputable section

/-! Transport the entire internal CM decomposition along an actual
rational Hodge comparison, including each summand's coefficient action. -/

variable {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U}

def cmComponentTransport (C : ComplexMultiplication.Decomposition.CM.CMComponent H) (e : U ≃ₗ[ℚ] V) : ComplexMultiplication.Decomposition.CM.CMComponent (H.transport e) := by
  let W := C.subspace.map e.toLinearMap
  let ei : C.subspace ≃ₗ[ℚ] W := Submodule.equivMapOfInjective e.toLinearMap e.injective C.subspace
  letI := ei.symm.toAddEquiv.module C.field
  letI := ei.symm.isScalarTower (A := C.field)
  have hlin : e.toLinearMap.comp (C.subspace.subtype.comp ei.symm.toLinearMap) = W.subtype := by
    ext x
    exact congrArg Subtype.val (ei.apply_symm_apply x)
  have hh := (H.transport_isHodgeMap e).comp
    (C.inclusion_hodge.comp (C.hodge.transport_symm_isHodgeMap ei))
  rw [hlin] at hh
  exact {
    subspace := W
    hodge := C.hodge.transport ei
    inclusion_hodge := hh
    field := C.field
    cm := Realization.rankOneCMAction_transport C.field C.cm ei }

def cmDecompositionTransport (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) (e : U ≃ₗ[ℚ] V) :
    ComplexMultiplication.Decomposition.CM.CMDecomposition (H.transport e) where
  numberOfComponents := D.numberOfComponents
  component i := cmComponentTransport (D.component i) e
  isInternal := by
    change DirectSum.IsInternal (fun i => (D.component i).subspace.map e.toLinearMap)
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact e.toLinearMap.iSupIndep_map e.injective D.isInternal.submodule_iSupIndep
    · rw [← Submodule.map_iSup, D.isInternal.submodule_iSup_eq_top, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.surjective

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Transport
