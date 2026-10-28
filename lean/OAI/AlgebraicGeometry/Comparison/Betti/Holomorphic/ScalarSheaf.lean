import OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel

/-! # Scalar Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarSheaf.Dolbeault

noncomputable section

/-! The native holomorphic functions, with their pointwise complex module
structure and their original restriction maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

def holomorphicScalarRestrict {U V : Opens M} (h : U ≤ V) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V) →ₗ[ℂ]
      DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) where
  toFun := ContMDiffMap.restrictAddMonoidHom 𝓘(ℂ, E) 𝓘(ℂ) ℂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def holomorphicScalarPresheaf : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj U := ModuleCat.of ℂ (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop))
  map h := ModuleCat.ofHom (holomorphicScalarRestrict E M (leOfHom h.unop))
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl

theorem holomorphicScalarPresheaf_isSheaf : (holomorphicScalarPresheaf E M).IsSheaf := by
  apply (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget (ModuleCat.{0} ℂ))).mpr
  exact (smoothSheaf 𝓘(ℂ, E) 𝓘(ℂ) M ℂ).property

def holomorphicScalarSheaf : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj := holomorphicScalarPresheaf E M
  property := holomorphicScalarPresheaf_isSheaf E M

def complexSheafForget : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) ⥤
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  sheafCompose (Opens.grothendieckTopology (TopCat.of M))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})

instance complexSheafForget_preservesZero : (complexSheafForget M).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance complexSheafForget_faithful : (complexSheafForget M).Faithful :=
  inferInstanceAs (sheafCompose (Opens.grothendieckTopology (TopCat.of M))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).Faithful

theorem holomorphicScalarSheaf_forget :
    (complexSheafForget M).obj (holomorphicScalarSheaf E M) = DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarSheaf.Dolbeault
