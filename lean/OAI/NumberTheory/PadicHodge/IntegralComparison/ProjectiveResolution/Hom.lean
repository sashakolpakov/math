import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Hom.Comparison

noncomputable section

/-! Ordinary Hom complexes of two genuine projective resolutions have
canonically isomorphic cohomology. No injectivity of the target module
is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

universe u v w z

def opposite {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (e : HomotopyEquiv K L) : HomotopyEquiv K.op L.op where
  hom := (HomologicalComplex.opFunctor C c).map e.inv.op
  inv := (HomologicalComplex.opFunctor C c).map e.hom.op
  homotopyHomInvId :=
    { hom := fun i j => (e.homotopyHomInvId.hom j i).op
      zero := fun i j hij => Quiver.Hom.unop_inj (e.homotopyHomInvId.zero j i hij)
      comm := fun n => Quiver.Hom.unop_inj (by
        change (e.hom ≫ e.inv).f n = prevD n e.homotopyHomInvId.hom +
          dNext n e.homotopyHomInvId.hom + 𝟙 (K.X n)
        exact (e.homotopyHomInvId.comm n).trans
          (congrArg (fun t => t + 𝟙 (K.X n)) (add_comm _ _))) }
  homotopyInvHomId :=
    { hom := fun i j => (e.homotopyInvHomId.hom j i).op
      zero := fun i j hij => Quiver.Hom.unop_inj (e.homotopyInvHomId.zero j i hij)
      comm := fun n => Quiver.Hom.unop_inj (by
        change (e.inv ≫ e.hom).f n = prevD n e.homotopyInvHomId.hom +
          dNext n e.homotopyInvHomId.hom + 𝟙 (L.X n)
        exact (e.homotopyInvHomId.comm n).trans
          (congrArg (fun t => t + 𝟙 (L.X n)) (add_comm _ _))) }

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : Cᵒᵖ ⥤ D) [F.Additive] {M : C} (P Q : ProjectiveResolution M)

def homotopyEquiv : HomotopyEquiv
    ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj P.complex.op)
    ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj Q.complex.op) :=
  F.mapHomotopyEquiv (opposite (ProjectiveResolution.homotopyEquiv P Q))

def homologyIso (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj P.complex.op).homology n) ≅
      (((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj Q.complex.op).homology n) :=
  (Comparison.homotopyEquiv F P Q).toHomologyIso n

def moduleHomologyIso {R : Type u} [CommRing R] {M : ModuleCat R}
    (P Q : ProjectiveResolution M) (N : ModuleCat R) (n : ℕ) :
    ((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.complex.op).homology n ≅
    ((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj Q.complex.op).homology n :=
  homologyIso ((linearYoneda R (ModuleCat R)).obj N) P Q n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Hom.Comparison
