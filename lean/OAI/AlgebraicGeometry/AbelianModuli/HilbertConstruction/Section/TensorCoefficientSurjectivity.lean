import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorCoefficientDetection

/-! # Tensor Coefficient Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorCoefficientSurjectivity

noncomputable section

/-! A coefficient map transports preimages for the actual section tensor pairing. In particular, a calculation using an affine test scheme's coordinate ring yields the native Cartesian comparison over its full ring of global functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {X Y : Scheme.{u}} {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules)
variable (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)
variable (hr : r.comp (algebraMap R C) = a.appTop.hom.comp f)

theorem moduleSectionTensorComparisonApp_change_map
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = q) (U : X.Opens) :
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M r hr U).comp
      (α.toLinearMap.rTensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (op U))) =
        Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U := by
  apply TensorProduct.ext'
  intro b x
  exact Module.TensorCoefficientChange.moduleSectionTensorComparisonApp_coefficient_change a f M q r hq hr α hα U b x

theorem moduleSectionTensor_surjective_of_coefficient_map
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = q) (U : X.Opens)
    (h : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U)) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M r hr U) := by
  intro y
  obtain ⟨x, hx⟩ := h y
  refine ⟨α.toLinearMap.rTensor ((Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (op U)) x, ?_⟩
  exact (LinearMap.congr_fun (moduleSectionTensorComparisonApp_change_map a f M q r hq hr α hα U) x).trans hx

theorem cartesian_sectionTensor_surjective_of_spec_pairing
    {S X P : Scheme.{u}} {B : Type u} [CommRing B]
    {a : P ⟶ X} {b : P ⟶ Spec (.of B)} {f : X ⟶ S} {g : Spec (.of B) ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    {R : Type u} [CommRing R] [Algebra R B] (c : R →+* Γ(X, ⊤))
    (hq : (b.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom).comp (algebraMap R B) =
      a.appTop.hom.comp c)
    (h : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom) hq ⊤)) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)) := by
  let : Algebra R (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    ((Scheme.ΓSpecIso (.of B)).inv.hom.comp (algebraMap R B)).toAlgebra
  let α : B →ₐ[R] (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    { toRingHom := (Scheme.ΓSpecIso (.of B)).inv.hom, commutes' := fun _ => rfl }
  have hr : b.appTop.hom.comp (algebraMap R (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) = a.appTop.hom.comp c := hq
  have hs : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      a c M b.appTop.hom hr ⊤) :=
    moduleSectionTensor_surjective_of_coefficient_map (B := B) (C := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a c M
      (b.appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom) b.appTop.hom hq hr α rfl ⊤ h
  exact TensorCoefficientDetection.cartesian_sectionTensor_surjective_of_coefficient_pairing H M c hr hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorCoefficientSurjectivity
