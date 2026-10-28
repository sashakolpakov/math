import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeHomology
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Base Change Quotient Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeQuotientCohomology

noncomputable section

/-! A flat base change carries cohomology supported on an ideal quotient to
the quotient by the extended ideal, with linearity over the new base ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]

def flatBaseChangeCohomologyQuotientIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ) (I : Ideal R)
    (e : C.homology g ≅ ModuleCat.of R (R ⧸ I)) :
    (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology g ≅
      ModuleCat.of B (B ⧸ I.map (algebraMap R B)) :=
  (BaseChangeHomology.flatBaseChangeHomologyIso C g).symm ≪≫
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapIso e ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.toModuleIso

theorem flatBaseChangeCohomology_vanish
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) (h : IsZero (C.homology q)) :
    IsZero ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology q) :=
  (Functor.map_isZero (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B) h).of_iso
    (BaseChangeHomology.flatBaseChangeHomologyIso C q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseChangeQuotientCohomology
