import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionSpanning
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison

/-! # Tensor Coefficient Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorCoefficientDetection

noncomputable section

/-! Surjectivity of the actual section pairing over an original coefficient ring implies surjectivity of the native Cartesian comparison over all functions on the base. The proof uses the same scalar functions and pulled-back sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

private def coefficientPushforwardTopSectionsAddEquiv
    {X Y : Scheme.{u}} {R : Type u} [CommRing R]
    (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : Y.Modules) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c ((Scheme.Modules.pushforward a).obj M)).obj (op ⊤) ≃+ Γ(M, ⊤) :=
  (Coefficient.PushforwardModuleComparison.coefficientPushforwardModuleComponent a c M ⊤).toAddEquiv

theorem cartesian_sectionTensor_surjective_of_coefficient_pairing
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    {R : Type u} [CommRing R] [Algebra R (Affine.TensorSectionComparison.morphismGlobalAlgebra g)]
    (c : R →+* Γ(X, ⊤))
    (hc : b.appTop.hom.comp (algebraMap R (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) = a.appTop.hom.comp c)
    (h : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      a c M b.appTop.hom hc ⊤)) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)) := by
  let L : P.Modules := (Scheme.Modules.pullback a).obj M
  let E := coefficientPushforwardTopSectionsAddEquiv a f.appTop.hom L
  let F : TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op ⊤)) →+ Γ(L, ⊤) :=
    E.toAddMonoidHom.comp ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)).hom.toAddMonoidHom
  intro y
  let t : Line.Bundles.structureModule P ⟶ L := (Global.Sections.moduleSectionHomEquiv L).symm (E y)
  obtain ⟨k, q, s, ht⟩ := Coefficient.SectionSpanning.coefficient_sections_spanned_of_tensor_surjective
    (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) a c M b.appTop.hom hc h t
  let x : Fin k → (Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op ⊤) :=
    fun i => Global.Sections.moduleSectionHomEquiv M (s i)
  refine ⟨∑ i, q i ⊗ₜ[Γ(S, ⊤)] x i, ?_⟩
  apply E.injective
  change F (∑ i, q i ⊗ₜ[Γ(S, ⊤)] x i) = E y
  let σ : Fin k → (Line.Bundles.structureModule P ⟶ L) :=
    fun i => Scalar.SectionValues.scalarSection (b.appTop (q i)) (Ample.LineBundles.pullbackSection a (s i))
  have hF (z : TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op ⊤))) :
      F z = E ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤) z) := rfl
  have hsum : (∑ i, F (q i ⊗ₜ[Γ(S, ⊤)] x i)) = ∑ i, Global.Sections.moduleSectionHomEquiv L (σ i) := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := Tensor.ScalarSectionValues.tensorComparison_scalarSectionValue H M (q i) (x i)
    have hi' : E ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)
        (q i ⊗ₜ[Γ(S, ⊤)] x i)) = Global.Sections.moduleSectionHomEquiv L (σ i) := by
      change (show Γ(L, ⊤) from (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)
        (q i ⊗ₜ[Γ(S, ⊤)] x i)) = Global.Sections.moduleSectionHomEquiv L (σ i)
      simpa only [x, σ, L, Equiv.symm_apply_apply] using hi
    exact (hF _).trans hi'
  have hs : (∑ i, Global.Sections.moduleSectionHomEquiv L (σ i)) = Global.Sections.moduleSectionHomEquiv L t :=
    (Module.SectionValueAdditive.moduleSectionHomEquiv_sum L Finset.univ σ).symm.trans
      (congrArg (Global.Sections.moduleSectionHomEquiv L) ht.symm)
  exact (map_sum F _ _).trans (hsum.trans (hs.trans ((Global.Sections.moduleSectionHomEquiv L).apply_symm_apply (E y))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.TensorCoefficientDetection
