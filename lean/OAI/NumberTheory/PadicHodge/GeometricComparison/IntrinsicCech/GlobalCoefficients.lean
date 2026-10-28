import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Global Coefficients -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalCoefficients.IntrinsicCechGlobalCoefficients

noncomputable section

/-! Evaluation of intersection coefficients at the whole scheme is naturally the original presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

abbrev Presheaves := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X.left

abbrev evaluate : Presheaves R X ⥤ ModuleCat.{0} R :=
  (CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)

def functor : Presheaves R X ⥤ Presheaves R X :=
  IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R X.left ⋙
    (Functor.whiskeringRight X.left.Opensᵒᵖ (Presheaves R X) (ModuleCat.{0} R)).obj (evaluate R X)

def iso : functor R X ≅ 𝟭 (Presheaves R X) :=
  NatIso.ofComponents (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R X) (by
    intro P Q f
    apply NatTrans.ext
    funext V
    exact (f.naturality (eqToHom (congrArg op (top_inf_eq (a := V.unop))))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalCoefficients.IntrinsicCechGlobalCoefficients
