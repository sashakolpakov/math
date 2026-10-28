import OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar

/-! # Spec Scalar Sections -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecScalarSections

noncomputable section

/-! The canonical section equivalence of an affine spectrum respects
the scalar algebra induced by its actual structure morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

def equivalence (K R : Type) [CommRing K] [CommRing R] [Algebra K R] :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K R))) ⊤
    R ≃ₐ[K] Γ(Spec (.of R), ⊤) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K R))) ⊤
  refine { Foundations.Scheme.FunctionFieldScalar.specGlobalScalarEquiv R with commutes' := ?_ }
  intro c
  change (Scheme.ΓSpecIso (.of R)).inv (algebraMap K R c) =
    (Spec.map (CommRingCat.ofHom (algebraMap K R))).appTop ((Scheme.ΓSpecIso (.of K)).inv c)
  exact congrArg (fun f : CommRingCat.of K ⟶ Γ(Spec (.of R), ⊤) => f c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K R)))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecScalarSections
