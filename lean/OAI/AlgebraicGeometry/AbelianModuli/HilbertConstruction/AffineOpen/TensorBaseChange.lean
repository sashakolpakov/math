import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialModuleTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.TensorComparisonReduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonPullbackCongruence

/-! # Tensor Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.TensorBaseChange

noncomputable section

/-! The actual module-section tensor comparison is invertible on every affine open where the module has a frame, after affine base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineFrame_moduleTensorComparison_isIso
    {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Line.Bundles.structureModule U.toScheme) :
    IsIso ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H M).app (.op U)) := by
  let j := U.ι
  let i := Limits.pullback.fst a j
  let c := Limits.pullback.snd a j
  let V := j ⁻¹ᵁ U
  let q : Affine.TensorSectionComparison.morphismGlobalAlgebra g →+* Γ(Limits.pullback a j, ⊤) := i.appTop.hom.comp b.appTop.hom
  have : IsAffine U.toScheme := hU
  have : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion (Limits.pullback.fst a j))
  have Hlocal : IsPullback c (i ≫ b) (j ≫ f) g :=
    (IsPullback.of_hasPullback a j).flip.paste_vert H
  have hVtop : V = ⊤ := by
    ext x
    exact iff_true_intro x.property
  have hV : IsAffineOpen V := (congrArg IsAffineOpen hVtop).mpr (isAffineOpen_top U.toScheme)
  have hij : i ≫ a = c ≫ j := Limits.pullback.condition
  have hqi : q.comp (algebraMap Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) = (i ≫ a).appTop.hom.comp f.appTop.hom :=
    Coefficient.PullbackRefinement.pullbackCoefficient_compatible_comp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) i a f.appTop.hom b.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H)
  have hqc : q.comp (algebraMap Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) = (c ≫ j).appTop.hom.comp f.appTop.hom :=
    hqi.trans (congrArg (fun z => z.appTop.hom.comp f.appTop.hom) hij)
  have hqc' : q.comp (algebraMap Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) =
      c.appTop.hom.comp (j.appTop.hom.comp f.appTop.hom) := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc] using hqc
  have hβ : Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      c (j ≫ f).appTop.hom ((Scheme.Modules.pullback j).obj M) (i ≫ b).appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility Hlocal) V) :=
    (ConcreteCategory.isIso_iff_bijective
      ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison Hlocal ((Scheme.Modules.pullback j).obj M)).app (.op V))).mp
      (TrivialModuleTensorComparison.affineOpen_trivialModuleTensorComparison_isIso Hlocal ((Scheme.Modules.pullback j).obj M) e V hV)
  have hf : (j ≫ f).appTop.hom = j.appTop.hom.comp f.appTop.hom := by ext r; rfl
  have hq : (i ≫ b).appTop.hom = q := by ext r; rfl
  have hlocal : Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      c (j.appTop.hom.comp f.appTop.hom) ((Scheme.Modules.pullback j).obj M) q hqc' V) :=
    (Tensor.ComparisonPullbackCongruence.moduleSectionTensorComparisonApp_bijective_congr (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) rfl hf
      ((Scheme.Modules.pullback j).obj M) hq (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility Hlocal) hqc' rfl).mp hβ
  have hUj : U ≤ j.opensRange := by
    simpa only [j, Scheme.Opens.opensRange_ι] using (le_refl U)
  have hc := Open.TensorComparisonReduction.moduleSectionTensorComparisonApp_bijective_of_open_comp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    c j f.appTop.hom M q hqc hqc' U hUj hlocal
  have hi : Function.Bijective (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
      (i ≫ a) f.appTop.hom M q hqi U) :=
    (Tensor.ComparisonPullbackCongruence.moduleSectionTensorComparisonApp_bijective_congr (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g) hij.symm rfl M rfl hqc hqi rfl).mp hc
  have hcover : a ⁻¹ᵁ U ≤ i.opensRange := by
    intro p hp
    let u : U.toScheme := ⟨a p, hp⟩
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback p u (show a p = j u from rfl)
    exact ⟨z, hz⟩
  have hbij := Open.TensorComparisonReduction.moduleSectionTensorComparisonApp_bijective_of_open_refine (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    i a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) U hcover hi
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.TensorBaseChange
