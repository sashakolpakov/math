import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.AlgebraPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSectionModules
import Mathlib.Algebra.Category.CommAlgCat.Monoidal

/-! # Section Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionComparison

noncomputable section

/-! The natural tensor comparison for functions on inverse images of opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {X P : Scheme.{u}} {R : Type u} [CommRing R]

def tensorAlgebraSectionComparisonApp (a : P ⟶ X) (f : R →+* Γ(X, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) (U : X.Opens) :
    B ⊗ Coefficient.AlgebraPresheaf.coefficientAlgebraSections f U ⟶
      Coefficient.AlgebraPresheaf.coefficientAlgebraSections (a.appTop.hom.comp f) (a ⁻¹ᵁ U) := by
  letI := (Coefficient.AlgebraPresheaf.coefficientSectionMap f U).toAlgebra
  letI := (Coefficient.AlgebraPresheaf.coefficientSectionMap (a.appTop.hom.comp f) (a ⁻¹ᵁ U)).toAlgebra
  let i : B →ₐ[R] Γ(P, a ⁻¹ᵁ U) :=
    (Coefficient.AlgebraPullback.coefficientAlgebraGlobalRestriction _ B q hq (a ⁻¹ᵁ U)).hom
  let j : Γ(X, U) →ₐ[R] Γ(P, a ⁻¹ᵁ U) := (Coefficient.AlgebraPullback.coefficientAlgebraPullbackApp a f U).hom
  exact CommAlgCat.ofHom (Algebra.TensorProduct.lift (R := R) (S := R) i j
    (fun _ _ => .all _ _))

theorem tensorAlgebraSectionComparisonApp_tmul (a : P ⟶ X) (f : R →+* Γ(X, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) (U : X.Opens)
    (b : B) (r : Coefficient.AlgebraPresheaf.coefficientAlgebraSections f U) :
    (tensorAlgebraSectionComparisonApp a f B q hq U).hom (b ⊗ₜ[R] r) =
      (Coefficient.AlgebraPullback.coefficientAlgebraGlobalRestriction _ B q hq (a ⁻¹ᵁ U)).hom b *
        (Coefficient.AlgebraPullback.coefficientAlgebraPullbackApp a f U).hom r := rfl

theorem tensorAlgebraSectionComparisonApp_naturality (a : P ⟶ X) (f : R →+* Γ(X, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)
    {U V : X.Opens} (h : V ≤ U) :
    B ◁ Coefficient.AlgebraPresheaf.coefficientAlgebraRestriction f h ≫ tensorAlgebraSectionComparisonApp a f B q hq V =
      tensorAlgebraSectionComparisonApp a f B q hq U ≫
        Coefficient.AlgebraPresheaf.coefficientAlgebraRestriction _ ((TopologicalSpace.Opens.map a.base).map (homOfLE h)).le := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro b r
  change (tensorAlgebraSectionComparisonApp a f B q hq V).hom
      (b ⊗ₜ[R] (Coefficient.AlgebraPresheaf.coefficientAlgebraRestriction f h).hom r) =
    (Coefficient.AlgebraPresheaf.coefficientAlgebraRestriction _
      ((TopologicalSpace.Opens.map a.base).map (homOfLE h)).le).hom
      ((tensorAlgebraSectionComparisonApp a f B q hq U).hom (b ⊗ₜ[R] r))
  rw [tensorAlgebraSectionComparisonApp_tmul, tensorAlgebraSectionComparisonApp_tmul, map_mul]
  congr 1
  · exact (congrArg (fun k => k.hom b)
      (Coefficient.AlgebraPullback.coefficientAlgebraGlobalRestriction_naturality _ B q hq
        ((TopologicalSpace.Opens.map a.base).map (homOfLE h)).le)).symm
  · exact congrArg (fun k => k r) (a.naturality (homOfLE h).op)

def tensorAlgebraSectionComparison (a : P ⟶ X) (f : R →+* Γ(X, ⊤))
    (B : CommAlgCat.{u} R) (q : B →+* Γ(P, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) :
    Coefficient.AlgebraPresheaf.coefficientAlgebraPresheaf f ⋙ tensorLeft B ⟶
      (TopologicalSpace.Opens.map a.base).op ⋙
        Coefficient.AlgebraPresheaf.coefficientAlgebraPresheaf (a.appTop.hom.comp f) where
  app U := tensorAlgebraSectionComparisonApp a f B q hq U.unop
  naturality _ _ h := tensorAlgebraSectionComparisonApp_naturality a f B q hq h.unop.le

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionComparison
