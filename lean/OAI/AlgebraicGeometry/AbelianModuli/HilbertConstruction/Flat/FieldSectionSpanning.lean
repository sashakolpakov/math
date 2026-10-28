import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.TensorSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Field Section Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FieldSectionSpanning

noncomputable section

/-! Flat base change to a field expresses every actual pulled-back line-bundle section as a finite coefficient linear combination of pulled-back original sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem flat_fieldPullback_sections_spanned
    {K : Type u} [Field K] {S X P : Scheme.{u}} [IsAffine S] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {f : X ⟶ S} {g : Spec (.of K) ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)]
    (t : Line.Bundles.structureModule P ⟶ (L.pullback a).sheaf) :
    ∃ (k : ℕ) (c : Fin k → K) (s : Fin k → (Line.Bundles.structureModule X ⟶ L.sheaf)),
      t = ∑ i, Coefficient.ScalarSections.coefficientScalarSection b (c i) (Ample.LineBundles.pullbackSection a (s i)) := by
  let F : TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (.op ⊤)) →+
        Γ((L.pullback a).sheaf, ⊤) :=
    ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ⊤)).hom.toAddMonoidHom
  have hF : Function.Surjective F := (BundleSectionBaseChange.flat_lineBundleTensorComparison_bijective H L).surjective
  obtain ⟨z, hz⟩ := hF (Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf t)
  obtain ⟨k, c, x, hzx⟩ := TensorProduct.exists_sum_tmul_eq z
  let d : Fin k → K := fun i => (Scheme.ΓSpecIso (.of K)).hom (c i)
  let s : Fin k → (Line.Bundles.structureModule X ⟶ L.sheaf) := fun i => (Global.Sections.moduleSectionHomEquiv L.sheaf).symm (x i)
  refine ⟨k, d, s, (Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf).injective ?_⟩
  calc
    Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf t = F z := hz.symm
    _ = F (∑ i, c i ⊗ₜ[Γ(S, ⊤)] x i) := congrArg F hzx
    _ = ∑ i, F (c i ⊗ₜ[Γ(S, ⊤)] x i) := map_sum F _ _
    _ = ∑ i, Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf
        (Coefficient.ScalarSections.coefficientScalarSection b (d i) (Ample.LineBundles.pullbackSection a (s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact HilbertConstruction.Field.TensorSectionValues.fieldTensorComparison_sectionValue H L.sheaf (c i) (x i)
    _ = Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf
        (∑ i, Coefficient.ScalarSections.coefficientScalarSection b (d i) (Ample.LineBundles.pullbackSection a (s i))) :=
      (HilbertConstruction.Module.SectionValueAdditive.moduleSectionHomEquiv_sum (L.pullback a).sheaf Finset.univ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FieldSectionSpanning
