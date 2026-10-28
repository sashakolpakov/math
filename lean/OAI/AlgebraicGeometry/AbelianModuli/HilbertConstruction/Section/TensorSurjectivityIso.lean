import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSheafNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.ModuleTensorComparison

/-! # Tensor Surjectivity Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorSurjectivityIso

noncomputable section

/-! Surjectivity of the actual section tensor comparison is preserved by a module-sheaf isomorphism. This allows a composed Poincare pullback to be identified with its iterated pullback without replacing either comparison map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

theorem moduleSectionTensorComparisonApp_surjective_of_iso
    {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
    {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (h : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq U)) :
    Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c N q hq U) := by
  let eS := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).mapIso e).app (op U)
  let eT := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).mapIso
    ((Scheme.Modules.pushforward a).mapIso ((Scheme.Modules.pullback a).mapIso e))).app (op U)
  let F := Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq U
  let G := Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c N q hq U
  let σ := TensorProduct.congr (LinearEquiv.refl R B) eS.toLinearEquiv
  have hc : G.comp σ.toLinearMap = eT.toLinearEquiv.toLinearMap.comp F := by
    apply TensorProduct.ext'
    intro b x
    exact Module.TensorSheafNaturality.moduleSectionTensorComparisonApp_sheaf_natural a c q hq e.hom U b x
  intro y
  obtain ⟨x, hx⟩ := h (eT.inv y)
  refine ⟨σ x, ?_⟩
  exact (LinearMap.congr_fun hc x).trans
    ((congrArg eT.hom hx).trans (eT.toLinearEquiv.apply_symm_apply y))

theorem baseChangeModuleTensorComparison_surjective_of_iso
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (h : Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op U))) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H N).app (op U)) :=
  moduleSectionTensorComparisonApp_surjective_of_iso (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    a f.appTop.hom b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) e U h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorSurjectivityIso
