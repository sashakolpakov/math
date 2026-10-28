import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Affine Section Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffineSectionSpanning

noncomputable section

/-! Flat affine base change expresses every actual line-bundle section as a finite linear combination of pulled-back sections with changed-base functions as coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem flat_affinePullback_sections_spanned
    {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) [Flat g]
    (t : Line.Bundles.structureModule P ⟶ (L.pullback a).sheaf) :
    ∃ (k : ℕ) (c : Fin k → Γ(Y, ⊤)) (s : Fin k → (Line.Bundles.structureModule X ⟶ L.sheaf)),
      t = ∑ i, Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i)) := by
  have : Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g) :=
    RingHom.flat_algebraMap_iff.mp g.flat_appTop
  let F : TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (.op ⊤)) →+
        Γ((L.pullback a).sheaf, ⊤) :=
    ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ⊤)).hom.toAddMonoidHom
  have hF : Function.Surjective F := (BundleSectionBaseChange.flat_lineBundleTensorComparison_bijective H L).surjective
  obtain ⟨z, hz⟩ := hF (Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf t)
  obtain ⟨k, c, x, hzx⟩ := TensorProduct.exists_sum_tmul_eq z
  let s : Fin k → (Line.Bundles.structureModule X ⟶ L.sheaf) := fun i => (Global.Sections.moduleSectionHomEquiv L.sheaf).symm (x i)
  refine ⟨k, c, s, (Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf).injective ?_⟩
  calc
    Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf t = F z := hz.symm
    _ = F (∑ i, c i ⊗ₜ[Γ(S, ⊤)] x i) := congrArg F hzx
    _ = ∑ i, F (c i ⊗ₜ[Γ(S, ⊤)] x i) := map_sum F _ _
    _ = ∑ i, Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf
        (Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Tensor.ScalarSectionValues.tensorComparison_scalarSectionValue H L.sheaf (c i) (x i)
    _ = Global.Sections.moduleSectionHomEquiv (L.pullback a).sheaf
        (∑ i, Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) :=
      (HilbertConstruction.Module.SectionValueAdditive.moduleSectionHomEquiv_sum (L.pullback a).sheaf Finset.univ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffineSectionSpanning
