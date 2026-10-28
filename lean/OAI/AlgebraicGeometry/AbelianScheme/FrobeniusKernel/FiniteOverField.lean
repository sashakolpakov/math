import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Finite Over Field -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteOverField.Construction

noncomputable section

/-! Finite schemes over the geometric residue field are finite locally free. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

/-- Over a field, the finite coordinate module is free. This applies to
the actual annihilator scheme, including when it is nonreduced. -/
theorem finiteOverField_finiteLocallyFree {K : Type u} [Field K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsFinite p] :
    Flat p ∧ LocallyOfFinitePresentation p := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let f : CommRingCat.of K ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)
  have hf : Spec.map f = X.isoSpec.inv ≫ p := Spec.map_preimage _
  have : IsFinite (Spec.map f) := (congrArg IsFinite hf).mpr inferInstance
  let : Algebra K Γ(X, ⊤) := f.hom.toAlgebra
  have : Module.Finite K Γ(X, ⊤) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff f).mp
      (inferInstanceAs (IsFinite (Spec.map f))))
  have hc := (CartierDuality.FiniteLocallyFreeCoordinates.Construction.finiteLocallyFree_spec_iff K Γ(X, ⊤)).mpr
    ⟨inferInstance, inferInstance⟩
  have : Flat (Spec.map f) := hc.2.1
  have : LocallyOfFinitePresentation (Spec.map f) := hc.2.2
  have h : X.isoSpec.hom ≫ Spec.map f = p := by
    rw [hf, ← Category.assoc, X.isoSpec.hom_inv_id, Category.id_comp]
  exact ⟨(congrArg Flat h).mp inferInstance,
    (congrArg LocallyOfFinitePresentation h).mp inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteOverField.Construction
