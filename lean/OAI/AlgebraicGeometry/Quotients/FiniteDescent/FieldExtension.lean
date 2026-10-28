import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Field Extension -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldExtension.Construction.FieldExtensionExact

noncomputable section

/-! Scalar extension from a field preserves homology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K]

theorem split_mono {M N : ModuleCat.{u} K} (f : M ⟶ N) [Mono f] : IsSplitMono f := by
  obtain ⟨g, hg⟩ := f.hom.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp inferInstance))
  exact ⟨⟨⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩⟩⟩

theorem preservesMonos {C : Type*} [Category C] (F : ModuleCat.{u} K ⥤ C) :
    F.PreservesMonomorphisms where
  preserves f _ := by
    have := split_mono f
    infer_instance

theorem preservesHomology_of_leftAdjoint {C : Type*} [Category C] [Abelian C]
    (F : ModuleCat.{u} K ⥤ C) [F.PreservesZeroMorphisms] [F.IsLeftAdjoint] :
    F.PreservesHomology := by
  have := preservesMonos F
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

theorem preservesHomology {R : Type u} [CommRing R] (f : K →+* R) :
    (ModuleCat.extendScalars f).PreservesHomology :=
  preservesHomology_of_leftAdjoint _

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldExtension.Construction.FieldExtensionExact
