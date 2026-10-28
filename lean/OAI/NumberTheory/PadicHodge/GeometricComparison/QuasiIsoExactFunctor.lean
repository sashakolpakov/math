import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiHom
import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedResolution

/-! # Quasi Iso Exact Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoExactFunctor.DerivedQuasiIsoExactFunctor

noncomputable section

/-! Linear quasi-isomorphism transport commutes with actual exact-functor maps on derived cohomology. -/

open _root_.CategoryTheory Limits

universe u u' v w w' t

variable (R : Type t) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [Linear R C]

theorem equiv_apply (A : C) {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (n : ℤ) (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n x = x ≫ (inv (DerivedCategory.Q.map f))⟦n⟧' := by
  simp only [DerivedQuasiHom.DerivedQuasiIsoHom.equiv, Linear.homCongr_symm_apply, Iso.refl_hom, Category.id_comp]
  rfl

variable {D : Type u'} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w'} D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (A : C)

theorem naturality {K K' : CochainComplex C ℤ} {L L' : CochainComplex D ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g]
    (a : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj K' ⟶ L')
    (h : (F.mapHomologicalComplex (.up ℤ)).map f ≫ b = a ≫ g)
    (n : ℤ) (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K')⟦n⟧) :
    DerivedQuasiHom.DerivedQuasiIsoHom.equiv R (F.obj A) g n (AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A b n x) =
      AcyclicExact.AcyclicExactFunctorNaturality.derivedMap F A a n (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n x) := by
  rw [equiv_apply, equiv_apply]
  exact DerivedResolution.DerivedResolutionExactNaturality.naturality F A f g a b h n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.QuasiIsoExactFunctor.DerivedQuasiIsoExactFunctor
