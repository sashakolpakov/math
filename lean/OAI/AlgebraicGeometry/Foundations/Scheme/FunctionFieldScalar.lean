import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import OAI.AlgebraicGeometry.Betti.AffineDimension

/-! # Function Field Scalar -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar

noncomputable section

/-!
# The canonical scalar structure on a scheme's function field

For an irreducible scheme over `Spec K`, scalar constants enter its function
field through the actual global-sections map and the germ at the generic point.
The compatibility with sections of every nonempty open is proved from the
sheaf restriction/germ identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K]

/-- The established identification of scalars with global functions on `Spec K`. -/
def specGlobalScalarEquiv : K ≃+* Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv

@[simp]
theorem specGlobalScalarEquiv_toRingHom :
    (specGlobalScalarEquiv K).toRingHom = (Scheme.ΓSpecIso (.of K)).inv.hom := rfl

/-- The actual scalar algebra structure on global functions of `Spec K`. -/
abbrev specGlobalScalarAlgebra : Algebra K Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra

variable {K} {X : Scheme.{u}} [IrreducibleSpace X]

/-- Scalar constants mapped by the structure morphism and then by the generic germ. -/
def functionFieldScalarMap (f : X ⟶ Spec (.of K)) : K →+* X.functionField :=
  (Betti.AffineDimension.Realization.functionFieldBaseMap f).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

/-- The canonical `K`-algebra structure on the actual function field of `X`. -/
abbrev functionFieldScalarAlgebra (f : X ⟶ Spec (.of K)) : Algebra K X.functionField :=
  (functionFieldScalarMap f).toAlgebra

/-- This map is explicitly the structure-map pullback followed by the generic germ. -/
@[simp]
theorem functionFieldScalarMap_apply (f : X ⟶ Spec (.of K)) (c : K) :
    functionFieldScalarMap f c =
      X.presheaf.germ ⊤ (genericPoint X) (by trivial)
        (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c)) := rfl

/-- Restricting a scalar section to a nonempty open before taking its generic germ
produces the same element of the function field. -/
theorem specSectionScalarMap_germ (f : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (SpecScalarTransport.specSectionScalarMap f U) =
      functionFieldScalarMap f := by
  exact congrArg
    (fun g : Γ(Spec (.of K), ⊤) ⟶ X.functionField =>
      g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (Betti.AffineDimension.Realization.sectionBaseMap_germ f U)

/-- Canonical scalar constants, sections, and the function field form a scalar tower. -/
theorem functionFieldScalar_isScalarTower (f : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    letI := functionFieldScalarAlgebra f
    IsScalarTower K Γ(X, U) X.functionField := by
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := functionFieldScalarAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  exact (specSectionScalarMap_germ f U).symm

/-- The scalar algebra is compatible with the original global-sections base algebra
used in the affine common-dimension theorem. -/
theorem functionFieldBaseScalar_isScalarTower (f : X ⟶ Spec (.of K)) :
    letI := specGlobalScalarAlgebra K
    letI := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
    letI := functionFieldScalarAlgebra f
    IsScalarTower K Γ(Spec (.of K), ⊤) X.functionField := by
  let := specGlobalScalarAlgebra K
  let := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
  let := functionFieldScalarAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The base map in this tower is a proved ring isomorphism, hence surjective. -/
theorem specGlobalScalarAlgebra_surjective :
    letI := specGlobalScalarAlgebra K
    Function.Surjective (algebraMap K Γ(Spec (.of K), ⊤)) := by
  exact (specGlobalScalarEquiv K).surjective

end

end OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar
