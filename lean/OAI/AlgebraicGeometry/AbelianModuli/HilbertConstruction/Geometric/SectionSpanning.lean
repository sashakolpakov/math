import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Section Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionSpanning

noncomputable section

/-! Surjectivity of the actual Cartesian section tensor comparison expresses sections as finite linear combinations of pulled-back sections and detects a nonvanishing summand. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g)

theorem geometric_sections_spanned_of_tensor_surjective (M : X.Modules)
    (h : Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)))
    (t : Line.Bundles.structureModule P ⟶ (Scheme.Modules.pullback a).obj M) :
    ∃ (k : ℕ) (c : Fin k → Γ(Y, ⊤)) (s : Fin k → (Line.Bundles.structureModule X ⟶ M)),
      t = ∑ i, Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i)) := by
  let F : TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op ⊤)) →+
        Γ((Scheme.Modules.pullback a).obj M, ⊤) :=
    ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (op ⊤)).hom.toAddMonoidHom
  have hF : Function.Surjective F := h
  obtain ⟨z, hz⟩ := hF (Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M) t)
  obtain ⟨k, c, x, hzx⟩ := TensorProduct.exists_sum_tmul_eq z
  let s : Fin k → (Line.Bundles.structureModule X ⟶ M) := fun i => (Global.Sections.moduleSectionHomEquiv M).symm (x i)
  refine ⟨k, c, s, (Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)).injective ?_⟩
  calc
    Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M) t = F z := hz.symm
    _ = F (∑ i, c i ⊗ₜ[Γ(S, ⊤)] x i) := congrArg F hzx
    _ = ∑ i, F (c i ⊗ₜ[Γ(S, ⊤)] x i) := map_sum F _ _
    _ = ∑ i, Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Tensor.ScalarSectionValues.tensorComparison_scalarSectionValue H M (c i) (x i)
    _ = Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (∑ i, Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) :=
      (Module.SectionValueAdditive.moduleSectionHomEquiv_sum ((Scheme.Modules.pullback a).obj M) Finset.univ _).symm

theorem exists_section_nonvanishing_of_tensor_surjective (L : Line.Bundles.LineBundle X)
    (h : Function.Surjective ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (op ⊤)))
    (y : P) (t : Line.Bundles.structureModule P ⟶ (L.pullback a).sheaf)
    (hy : y ∈ Ample.LineBundles.sectionNonvanishing t) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, a y ∈ Ample.LineBundles.sectionNonvanishing s := by
  obtain ⟨k, c, s, ht⟩ := geometric_sections_spanned_of_tensor_surjective H L.sheaf h t
  have hy' : y ∈ Ample.LineBundles.sectionNonvanishing (∑ i, Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) :=
    (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) ht).mp hy
  obtain ⟨i, _, hi⟩ := (L.pullback a).mem_sectionNonvanishing_sum Finset.univ
    (fun i => Scalar.SectionValues.scalarSection (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i))) y hy'
  have hiy := Scalar.SectionNonvanishing.scalarSection_nonvanishing_le (L.pullback a) (b.appTop (c i)) (Ample.LineBundles.pullbackSection a (s i)) hi
  exact ⟨s i, (congrArg (fun V : P.Opens => y ∈ V)
    (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a L (s i))).mp hiy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.SectionSpanning
