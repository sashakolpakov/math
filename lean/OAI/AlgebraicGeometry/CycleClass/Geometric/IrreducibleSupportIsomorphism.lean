import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportIsomorphism

/-! # Irreducible Support Isomorphism -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.IrreducibleSupportIsomorphism

noncomputable section

/-!
# Actual irreducible supports under scheme isomorphisms

The support map is the ordinary set-theoretic image under the underlying
scheme isomorphism. This ungraded construction is independent of either
specialization coheight or function-field dimension. It is the common base
for the reduced-support scheme isomorphism and the dimension-graded cycle
transport.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y Z : Scheme.{u}}

/-- The actual closed image of an irreducible support under a scheme isomorphism. -/
def irreducibleSupportIsoImage (e : X ≅ Y) (S : IrreducibleCloseds X) :
    IrreducibleCloseds Y :=
  ⟨e.hom '' (S : Set X), S.isIrreducible.image _ e.hom.continuous.continuousOn,
    (Scheme.homeoOfIso e).isClosedMap _ S.isClosed⟩

/-- Scheme isomorphisms relabel all actual irreducible closed supports. -/
def irreducibleSupportIsoEquiv (e : X ≅ Y) :
    IrreducibleCloseds X ≃ IrreducibleCloseds Y where
  toFun := irreducibleSupportIsoImage e
  invFun := irreducibleSupportIsoImage e.symm
  left_inv S := by
    apply IrreducibleCloseds.ext
    exact (Scheme.homeoOfIso e).toEquiv.symm_image_image (S : Set X)
  right_inv S := by
    apply IrreducibleCloseds.ext
    exact (Scheme.homeoOfIso e).toEquiv.image_symm_image (S : Set Y)

@[simp]
theorem irreducibleSupportIsoEquiv_coe (e : X ≅ Y) (S : IrreducibleCloseds X) :
    (irreducibleSupportIsoEquiv e S : Set Y) = e.hom '' (S : Set X) :=
  rfl

@[simp]
theorem irreducibleSupportIsoEquiv_symm (e : X ≅ Y) :
    (irreducibleSupportIsoEquiv e).symm = irreducibleSupportIsoEquiv e.symm := by
  apply Equiv.ext
  intro S
  rfl

@[simp]
theorem irreducibleSupportIsoEquiv_refl :
    irreducibleSupportIsoEquiv (Iso.refl X) = Equiv.refl (IrreducibleCloseds X) := by
  apply Equiv.ext
  intro S
  apply IrreducibleCloseds.ext
  exact Set.image_id (S : Set X)

@[simp]
theorem irreducibleSupportIsoEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    irreducibleSupportIsoEquiv (e.trans f) =
      (irreducibleSupportIsoEquiv e).trans (irreducibleSupportIsoEquiv f) := by
  apply Equiv.ext
  intro S
  apply IrreducibleCloseds.ext
  exact (Set.image_image f.hom e.hom (S : Set X)).symm

/-- The generic point is carried by the same actual scheme isomorphism. -/
@[simp]
theorem irreducibleSupportIsoEquiv_genericPoint (e : X ≅ Y)
    (S : IrreducibleCloseds X) :
    irreducibleSetEquivPoints (irreducibleSupportIsoEquiv e S) =
      e.hom (irreducibleSetEquivPoints S) := by
  have hc : IsClosed (e.hom '' (S : Set X)) := (irreducibleSupportIsoEquiv e S).isClosed
  have h : IsGenericPoint (e.hom (irreducibleSetEquivPoints S))
      (irreducibleSupportIsoEquiv e S : Set Y) := by
    change IsGenericPoint (e.hom S.isIrreducible.genericPoint) (e.hom '' (S : Set X))
    simpa only [hc.closure_eq] using
      (S.isIrreducible.isGenericPoint_genericPoint S.isClosed).image e.hom.continuous
  exact (h.eq ((irreducibleSupportIsoEquiv e S).isIrreducible.isGenericPoint_genericPoint
    (irreducibleSupportIsoEquiv e S).isClosed)).symm

/-- The earlier coheight-graded support map has this same underlying image.
This is an agreement of support maps, not an identification of dimension gradings. -/
theorem irreducibleCycleSupportIsoEquiv_underlying (e : X ≅ Y) (p : ℕ)
    (S : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) :
    (SupportIsomorphism.irreducibleCycleSupportIsoEquiv e p S).1 = irreducibleSupportIsoEquiv e S.1 := by
  apply IrreducibleCloseds.ext
  exact SupportIsomorphism.irreducibleCycleSupportIsoEquiv_coe e p S

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.IrreducibleSupportIsomorphism
