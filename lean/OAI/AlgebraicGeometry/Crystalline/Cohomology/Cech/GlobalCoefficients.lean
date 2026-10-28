import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Global Coefficients -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalCoefficients.CechGlobalCoefficients

noncomputable section

/-! Evaluation of intersection coefficients at the whole scheme is naturally the original presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

abbrev Presheaves := Presheaf.CechPresheaf.Presheaves R X.left

abbrev evaluate : Presheaves R X ⥤ ModuleCat.{u} R :=
  (CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)

def functor : Presheaves R X ⥤ Presheaves R X :=
  MixedCech.Functor.MixedCechFunctor.coefficients R X.left ⋙
    (Functor.whiskeringRight X.left.Opensᵒᵖ (Presheaves R X) (ModuleCat.{u} R)).obj (evaluate R X)

def iso : functor R X ≅ 𝟭 (Presheaves R X) :=
  NatIso.ofComponents (GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R X) (by
    intro P Q f
    apply NatTrans.ext
    funext V
    exact (f.naturality (eqToHom (congrArg op (top_inf_eq (a := V.unop))))).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalCoefficients.CechGlobalCoefficients
