import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechPresheafSheaf

/-! # Cech Unit Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechUnitNaturality.LargeZariskiCechUnitNaturality

noncomputable section

/-! # The canonical Čech sheafification isomorphism is natural in the coefficient sheaf -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens)

theorem naturality {F F' : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)}
    (f : F ⟶ F') :
    (MixedCech.Functor.MixedCechFunctor.functor R X U).map f.hom ≫ CechPresheafSheaf.LargeZariskiCechPresheafSheaf.unit R X F' U =
      CechPresheafSheaf.LargeZariskiCechPresheafSheaf.unit R X F U ≫
        ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).unit.naturality
    (((MixedCech.Functor.MixedCechFunctor.functor R X U).map f.hom).f n)

def iso :
    sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) ⋙
      MixedCech.Functor.MixedCechFunctor.functor R X U ≅
        MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U ⋙
          (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).mapHomologicalComplex
            (ComplexShape.up ℕ) :=
  NatIso.ofComponents (fun F => CechPresheafSheaf.LargeZariskiCechPresheafSheaf.iso R X F U)
    (by intro F F' f; exact LargeZariskiCechUnitNaturality.naturality R X U f)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechUnitNaturality.LargeZariskiCechUnitNaturality
