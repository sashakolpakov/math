import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ResidueSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.DifferentialTensorKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionTensorModelCriterion

/-! # Model Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelSectionBaseChange

noncomputable section

/-! If the first differential in a minimal short-complex model is zero, the original differential has a generalized inverse. Consequently its actual geometric section tensor comparison is surjective after every prescribed base change. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

namespace LocalSectionLifting

theorem shortComplex_first_generalizedInverse_of_equiv_zero
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)}
    (e : ShortComplex.HomotopyEquiv S T)
    (h₀ : e.homotopyHomInvId.h₀ = 0) (hf : T.f = 0) :
    ∃ r : S.X₂ →ₗ[R] S.X₁, S.f.hom.comp (r.comp S.f.hom) = S.f.hom := by
  let h := e.homotopyHomInvId
  have hinv : e.inv.τ₁ ≫ S.f = 0 := by
    rw [e.inv.comm₁₂, hf, zero_comp]
  have hm := congrArg (fun z : S.X₁ ⟶ S.X₁ => z ≫ S.f) h.comm₁
  change (e.hom.τ₁ ≫ e.inv.τ₁) ≫ S.f =
    ((S.f ≫ h.h₁ + h.h₀) + 𝟙 S.X₁) ≫ S.f at hm
  have hzero : h.h₀ = 0 := h₀
  simp only [hzero, add_zero, Preadditive.add_comp, Category.id_comp,
    Category.assoc, hinv, comp_zero] at hm
  have hz : S.f ≫ h.h₁ ≫ S.f = -S.f := eq_neg_iff_add_eq_zero.mpr hm.symm
  have hg : S.f ≫ (-h.h₁) ≫ S.f = S.f := by
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    rw [hz, neg_neg]
  exact ⟨-h.h₁.hom, ModuleCat.hom_ext_iff.mp hg⟩

theorem minimal_baseChange_first_generalizedInverse
    {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    {S : ShortComplex (ModuleCat.{u} R)} (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)
    (hQ : Q.complex.f.hom.baseChange B = 0) :
    ∃ r : (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S).X₂ →ₗ[B] (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S).X₁,
      (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S).f.hom.comp
        (r.comp (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S).f.hom) = (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S).f.hom := by
  let F := Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  exact shortComplex_first_generalizedInverse_of_equiv_zero
    (ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMap F Q.equivalence)
    (ShortComplexEndpointHomotopy.LocalSectionLifting.shortComplexHomotopyEquivMap_hom_h₀ F Q.equivalence Q.hom_h₀)
    (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_f_zero R B Q.complex hQ)

end LocalSectionLifting

theorem geometric_sectionTensor_surjective_of_shortComplex_zero_model
    {S X Y P : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H M U) 0]
    {T : ShortComplex (ModuleCat.{u} Γ(S, ⊤))}
    (e : ShortComplex.HomotopyEquiv (D.sc' 0 1 2) T)
    (h₀ : e.homotopyHomInvId.h₀ = 0) (hT : T.f = 0) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)) := by
  obtain ⟨r, hr⟩ := LocalSectionLifting.shortComplex_first_generalizedInverse_of_equiv_zero e h₀ hT
  apply Geometric.SectionTensorModelCriterion.geometric_sectionTensor_surjective_of_model_kernel_range H M U hU φ
  exact Regular.DifferentialTensorKernel.tensor_kernel_range_of_generalizedInverse (D.d 0 1).hom r hr (Affine.TensorSectionComparison.morphismGlobalAlgebra g)

theorem geometric_sectionTensor_surjective_of_minimal_first_zero
    {S X Y P : Scheme.{u}} [IsLocalRing Γ(S, ⊤)]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom M U)
    [QuasiIsoAt φ 0]
    [QuasiIsoAt (Module.TensorFunctor.ModuleTensorFunctor.map (Affine.TensorSectionComparison.morphismGlobalAlgebra g) φ ≫
      Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H M U) 0]
    (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex (D.sc' 0 1 2))
    (hQ : Q.complex.f = 0) :
    Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)) := by
  exact geometric_sectionTensor_surjective_of_shortComplex_zero_model H M U hU φ
    Q.equivalence Q.hom_h₀ hQ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelSectionBaseChange
