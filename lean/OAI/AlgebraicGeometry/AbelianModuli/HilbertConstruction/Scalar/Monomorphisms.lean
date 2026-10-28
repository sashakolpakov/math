import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulScalarExactness
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-! # Monomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Monomorphisms

noncomputable section

/-! Monomorphisms transport through scalar-extension comparison isomorphisms and descend along faithfully flat scalar maps. -/
open _root_.CategoryTheory
universe u v w

theorem mono_map_iff_of_functor_iso
    {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D] {F G : C ⥤ D}
    (e : F ≅ G) {M N : C} (i : M ⟶ N) : Mono (F.map i) ↔ Mono (G.map i) :=
  (MorphismProperty.monomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (e.app M) (e.app N) (e.hom.naturality i).symm)

theorem native_iterated_scalar_mono_iff
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    {M N : ModuleCat.{u} R} (i : M ⟶ N) :
    Mono ((ModuleCat.extendScalars ((algebraMap A B).comp (algebraMap R A))).map i) ↔
      Function.Injective ((i.hom.baseChange A).baseChange B) := by
  have h := mono_map_iff_of_functor_iso (Iterated.TensorExactness.iteratedTensorScalarIso (R := R) (A := A) (B := B)) i
  exact h.trans (ModuleCat.mono_iff_injective _)

theorem native_scalar_mono_iff_of_faithfullyFlat
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : f.FaithfullyFlat) {M N : ModuleCat.{u} R} (i : M ⟶ N) :
    Mono ((ModuleCat.extendScalars f).map i) ↔ Mono i := by
  let : Algebra R A := f.toAlgebra
  have : Module.FaithfullyFlat R A := hf
  rw [ModuleCat.mono_iff_injective, ModuleCat.mono_iff_injective]
  exact Module.FaithfullyFlat.lTensor_injective_iff_injective R A i.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Monomorphisms
