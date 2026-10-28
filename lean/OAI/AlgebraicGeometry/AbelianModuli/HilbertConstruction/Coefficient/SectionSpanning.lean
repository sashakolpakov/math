import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionNonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LinearCombinationNonvanishing
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Section Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionSpanning

noncomputable section

/-! Surjective section comparison over any original coefficient ring expresses actual pulled-back sections as finite scalar combinations. This permits quotient and residue comparisons without discarding the actual sheaf pullback or scalar functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)

theorem coefficientTensorComparison_scalarSectionValue (b : B)
    (x : (ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤)) :
    (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤ (b ⊗ₜ[R] x)) =
      Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (Scalar.SectionValues.scalarSection (q b) (Ample.LineBundles.pullbackSection a ((Global.Sections.moduleSectionHomEquiv M).symm x))) := by
  have hv := (Pullback.SectionGlobalValue.pullbackSection_globalValue a ((Global.Sections.moduleSectionHomEquiv M).symm x)).trans
    (congrArg (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤)
      ((Global.Sections.moduleSectionHomEquiv M).apply_symm_apply x))
  have hs := (Scalar.SectionValues.scalarSection_globalValue (q b)
    (Ample.LineBundles.pullbackSection a ((Global.Sections.moduleSectionHomEquiv M).symm x))).trans
      (congrArg (fun v : Γ((Scheme.Modules.pullback a).obj M, ⊤) => q b • v) hv)
  have h := Module.TensorSectionValues.moduleSectionTensorComparisonApp_value a c M q hq ⊤ b x
  change (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤ (b ⊗ₜ[R] x)) =
    (Y.presheaf.map (𝟙 (op (⊤ : Y.Opens))) (q b)) •
      (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x) at h
  have h' : (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
      Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤ (b ⊗ₜ[R] x)) =
      q b • (show Γ((Scheme.Modules.pullback a).obj M, ⊤) from
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ x) := by
    simpa only [Y.presheaf.map_id, CommRingCat.id_apply] using h
  exact h'.trans hs.symm

theorem coefficient_sections_spanned_of_tensor_surjective
    (h : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤))
    (t : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback a).obj M) :
    ∃ (k : ℕ) (b : Fin k → B) (s : Fin k → (Line.Bundles.structureModule X ⟶ M)),
      t = ∑ i, Scalar.SectionValues.scalarSection (q (b i)) (Ample.LineBundles.pullbackSection a (s i)) := by
  let F : TensorProduct R B ((ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤)) →+
      Γ((Scheme.Modules.pullback a).obj M, ⊤) :=
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c M q hq ⊤).toAddMonoidHom
  obtain ⟨z, hz⟩ := h (Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M) t)
  obtain ⟨k, b, x, hzx⟩ := TensorProduct.exists_sum_tmul_eq z
  let s : Fin k → (Line.Bundles.structureModule X ⟶ M) := fun i => (Global.Sections.moduleSectionHomEquiv M).symm (x i)
  refine ⟨k, b, s, (Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)).injective ?_⟩
  calc
    Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M) t = F z := hz.symm
    _ = F (∑ i, b i ⊗ₜ[R] x i) := congrArg F hzx
    _ = ∑ i, F (b i ⊗ₜ[R] x i) := map_sum F _ _
    _ = ∑ i, Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (Scalar.SectionValues.scalarSection (q (b i)) (Ample.LineBundles.pullbackSection a (s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact coefficientTensorComparison_scalarSectionValue a c M q hq (b i) (x i)
    _ = Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)
        (∑ i, Scalar.SectionValues.scalarSection (q (b i)) (Ample.LineBundles.pullbackSection a (s i))) :=
      (Module.SectionValueAdditive.moduleSectionHomEquiv_sum ((Scheme.Modules.pullback a).obj M) Finset.univ _).symm

theorem coefficient_exists_section_nonvanishing_of_tensor_surjective
    (L : Line.Bundles.LineBundle X)
    (h : Function.Surjective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a c L.sheaf q hq ⊤))
    (y : Y) (t : Line.Bundles.structureModule Y ⟶ (L.pullback a).sheaf)
    (hy : y ∈ Ample.LineBundles.sectionNonvanishing t) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, a y ∈ Ample.LineBundles.sectionNonvanishing s := by
  obtain ⟨k, b, s, ht⟩ := coefficient_sections_spanned_of_tensor_surjective a c L.sheaf q hq h t
  have hy' : y ∈ Ample.LineBundles.sectionNonvanishing (∑ i, Scalar.SectionValues.scalarSection (q (b i)) (Ample.LineBundles.pullbackSection a (s i))) :=
    (congrArg (fun z => y ∈ Ample.LineBundles.sectionNonvanishing z) ht).mp hy
  obtain ⟨i, _, hi⟩ := (L.pullback a).mem_sectionNonvanishing_sum Finset.univ
    (fun i => Scalar.SectionValues.scalarSection (q (b i)) (Ample.LineBundles.pullbackSection a (s i))) y hy'
  have hiy := Scalar.SectionNonvanishing.scalarSection_nonvanishing_le (L.pullback a) (q (b i)) (Ample.LineBundles.pullbackSection a (s i)) hi
  exact ⟨s i, (congrArg (fun V : Y.Opens => y ∈ V)
    (LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange a L (s i))).mp hiy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionSpanning
