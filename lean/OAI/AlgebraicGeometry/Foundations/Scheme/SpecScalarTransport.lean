import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Spec Scalar Transport -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

noncomputable section

/-!
# Transport from global functions on Spec to the actual scalar ring

A morphism to `Spec K` induces a map from `Γ(Spec K, ⊤)` on each open's
sections. Composing with the canonical, proved inverse `K → Γ(Spec K, ⊤)`
gives the intended scalar structure. Standard smooth relative dimension is
unchanged, and the resulting affine structure morphism agrees with the
restriction of the original scheme morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- The actual scalar homomorphism on sections of a scheme over `Spec K`. -/
def specSectionScalarMap (f : X ⟶ Spec (.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

/-- The `K`-algebra structure induced by the actual structure morphism. -/
abbrev specSectionScalarAlgebra (f : X ⟶ Spec (.of K)) (U : X.Opens) :
    Algebra K Γ(X, U) :=
  (specSectionScalarMap f U).toAlgebra

/-- Replacing `Γ(Spec K, ⊤)` by `K` through its canonical isomorphism preserves
standard smoothness with its exact relative dimension. -/
theorem specSectionScalarMap_standardSmooth_iff (d : ℕ)
    (f : X ⟶ Spec (.of K)) (U : X.Opens) :
    RingHom.IsStandardSmoothOfRelativeDimension d (specSectionScalarMap f U) ↔
      RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ U le_top).hom := by
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)).cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)

/-- The same transport stated directly for the two explicit algebra structures. -/
theorem specSectionScalarAlgebra_standardSmooth_iff (d : ℕ)
    (f : X ⟶ Spec (.of K)) (U : X.Opens) :
    letI := (f.appLE ⊤ U le_top).hom.toAlgebra
    letI := specSectionScalarAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, U) ↔
      Algebra.IsStandardSmoothOfRelativeDimension d Γ(Spec (.of K), ⊤) Γ(X, U) := by
  exact specSectionScalarMap_standardSmooth_iff d f U

/-- A standard smooth chart over the global functions of `Spec K` is therefore
standard smooth of the same dimension over the intended scalar ring. -/
theorem specSectionScalarAlgebra_standardSmooth (d : ℕ)
    (f : X ⟶ Spec (.of K)) (U : X.Opens)
    (h : RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ U le_top).hom) :
    letI := specSectionScalarAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, U) :=
  (specSectionScalarMap_standardSmooth_iff d f U).mpr h

/-- On an actual affine open, the transported scalar algebra's structural
morphism is exactly the original structural morphism restricted to that open. -/
theorem specSectionScalarMap_fromSpec (f : X ⟶ Spec (.of K))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (specSectionScalarMap f U)) = hU.fromSpec ≫ f := by
  simpa only [specSectionScalarMap, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of K))) hU le_top)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
