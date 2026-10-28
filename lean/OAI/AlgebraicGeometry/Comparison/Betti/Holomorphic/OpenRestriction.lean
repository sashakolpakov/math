import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarSheaf
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenRestriction.Dolbeault

noncomputable section

/-! Restricting the native holomorphic function sheaf to an open manifold
gives its native function sheaf, by the actual inclusion of open subsets. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : TopCat.{0}} [ChartedSpace E M]

def nestedOpenImageHomeomorph (U : Opens M) (V : Opens U) :
    V ≃ₜ U.isOpenEmbedding.functor.obj V :=
  U.isOpenEmbedding.isEmbedding.homeomorphImage (V : Set U)

theorem nestedOpenImageHomeomorph_apply_val (U : Opens M) (V : Opens U) (x : V) :
    (nestedOpenImageHomeomorph U V x).val = x.val.val := rfl

theorem nestedOpenImageHomeomorph_symm_apply_val (U : Opens M) (V : Opens U)
    (y : U.isOpenEmbedding.functor.obj V) :
    ((nestedOpenImageHomeomorph U V).symm y).val.val = y.val :=
  congrArg Subtype.val ((nestedOpenImageHomeomorph U V).apply_symm_apply y)

theorem nestedOpenImageHomeomorph_holomorphic (U : Opens M) (V : Opens U) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (nestedOpenImageHomeomorph U V) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (U := U)).comp
    (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (U := V))

theorem nestedOpenImageHomeomorph_symm_holomorphic (U : Opens M) (V : Opens U) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (nestedOpenImageHomeomorph U V).symm := by
  rw [← ContMDiff.subtypeVal_comp_iff, ← ContMDiff.subtypeVal_comp_iff]
  exact (contMDiff_subtype_val (I := 𝓘(ℂ, E))
    (U := U.isOpenEmbedding.functor.obj V)).congr
      (nestedOpenImageHomeomorph_symm_apply_val U V)

def holomorphicNestedOpenSectionEquiv (U : Opens M) (V : Opens U) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.isOpenEmbedding.functor.obj V) ≃ₗ[ℂ]
      DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V) where
  toFun f := ⟨fun x => f (nestedOpenImageHomeomorph U V x),
    f.contMDiff.comp (nestedOpenImageHomeomorph_holomorphic U V)⟩
  invFun g := ⟨fun y => g ((nestedOpenImageHomeomorph U V).symm y),
    g.contMDiff.comp (nestedOpenImageHomeomorph_symm_holomorphic U V)⟩
  left_inv f := by
    apply ContMDiffMap.ext
    intro y
    exact congrArg f ((nestedOpenImageHomeomorph U V).apply_symm_apply y)
  right_inv g := by
    apply ContMDiffMap.ext
    intro x
    exact congrArg g ((nestedOpenImageHomeomorph U V).symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def holomorphicScalarSheaf_restrictIso (U : Opens M) :
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict (ModuleCat.{0} ℂ) U.isOpenEmbedding).obj
        (ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M) ≅ ScalarSheaf.Dolbeault.holomorphicScalarSheaf E U :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V => (holomorphicNestedOpenSectionEquiv U V.unop).toModuleIso) (by
      intro V W h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply ContMDiffMap.ext
      intro x
      rfl))

def holomorphicFunctionSheaf_restrictIso (U : Opens M) :
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} U.isOpenEmbedding).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) ≅ DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E U :=
  (ScalarSheaf.Dolbeault.complexSheafForget U).mapIso (holomorphicScalarSheaf_restrictIso U)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenRestriction.Dolbeault
