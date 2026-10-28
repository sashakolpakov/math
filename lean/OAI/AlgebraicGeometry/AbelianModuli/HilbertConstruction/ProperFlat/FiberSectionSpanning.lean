import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Fiber Section Spanning -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionSpanning

noncomputable section

/-! First fiber cohomology vanishing expresses every fiber section as an actual finite linear combination of pulled-back global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem properFlat_fiber_sections_spanned
    {S X : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x : S)
    (hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (f.fiberι x)).sheaf 1))
    (t : Line.Bundles.structureModule (f.fiber x) ⟶ (L.pullback (f.fiberι x)).sheaf) :
    ∃ (k : ℕ) (c : Fin k → Γ(Spec (S.residueField x), ⊤))
      (s : Fin k → (Line.Bundles.structureModule X ⟶ L.sheaf)),
      t = ∑ i, Scalar.SectionValues.scalarSection ((f.fiberToSpecResidueField x).appTop (c i))
        (Ample.LineBundles.pullbackSection (f.fiberι x) (s i)) := by
  let Y := Spec (S.residueField x)
  let P := f.fiber x
  let a := f.fiberι x
  let b := f.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x
  let H := IsPullback.of_hasPullback f g
  let F : TensorProduct Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom L.sheaf).obj (.op ⊤)) →+
        Γ((L.pullback a).sheaf, ⊤) :=
    ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app (.op ⊤)).hom.toAddMonoidHom
  have hF : Function.Surjective F := FiberSectionBaseChange.properFlat_fiberSectionTensorComparison_surjective f L x hH
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
      (Module.SectionValueAdditive.moduleSectionHomEquiv_sum (L.pullback a).sheaf Finset.univ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionSpanning
