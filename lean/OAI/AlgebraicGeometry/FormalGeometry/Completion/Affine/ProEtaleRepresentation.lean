import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Algebras

/-! # Pro Etale Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProEtaleRepresentation.Construction

noncomputable section

/-!
# Completion: recovering actual affine site objects from their algebras

An affine object over Spec R is the spectrum of its actual global sections,
with the R-algebra structure determined by its original structure morphism.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]
  (U : (Spec (CommRingCat.of R)).ProEt) [IsAffine U.left]

/-- Global sections with the algebra structure induced by the original site object. -/
def proEtaleAlgebraOfAffine : ProEtale.Algebras.Construction.ProEtaleAlgebra R := by
  let g := Spec.preimage (U.left.isoSpec.inv ≫ U.hom)
  letI : Algebra R Γ(U.left, ⊤) := g.hom.toAlgebra
  refine ⟨CommAlgCat.of R Γ(U.left, ⊤), ?_⟩
  change WeaklyEtale (Spec.map (Spec.preimage (U.left.isoSpec.inv ≫ U.hom)))
  rw [Spec.map_preimage]
  infer_instance

/-- The affine algebra representation recovers the actual object over the original base. -/
def proEtaleAlgebraOfAffineIso :
    (ProEtale.Algebras.Construction.proEtaleAlgebraSpec R).obj (op (proEtaleAlgebraOfAffine U)) ≅ U :=
  MorphismProperty.Over.isoMk U.left.isoSpec.symm (by
    change U.left.isoSpec.inv ≫ U.hom =
      Spec.map (Spec.preimage (U.left.isoSpec.inv ≫ U.hom))
    exact (Spec.map_preimage _).symm)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProEtaleRepresentation.Construction
