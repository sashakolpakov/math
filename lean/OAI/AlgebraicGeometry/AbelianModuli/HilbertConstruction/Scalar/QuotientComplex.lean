import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.RingTheory.QuotSMulTop
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.RegularCategory
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

/-! # Quotient Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.QuotientComplex

noncomputable section

/-! Scalar reduction of a cochain complex, its tensor description, and the actual short exact sequence associated to a scalar regular on every term. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

def moduleScalarQuotientFunctor (r : R) : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (QuotSMulTop r M)
  map f := ModuleCat.ofHom (QuotSMulTop.map r f.hom)
  map_id M := ModuleCat.hom_ext (QuotSMulTop.map_id r M)
  map_comp f g := ModuleCat.hom_ext (QuotSMulTop.map_comp r g.hom f.hom)

instance moduleScalarQuotientFunctor_additive (r : R) : (moduleScalarQuotientFunctor r).Additive where
  map_add {_X _Y f g} := ModuleCat.hom_ext ((QuotSMulTop.map r).map_add f.hom g.hom)

def moduleScalarQuotientTensorIso (r : R) :
    moduleScalarQuotientFunctor r ≅ Module.TensorFunctor.ModuleTensorFunctor.tensor (R ⧸ Ideal.span {r}) := by
  refine NatIso.ofComponents (fun M => (QuotSMulTop.equivQuotTensor r M).toModuleIso) ?_
  intro M N f
  apply ModuleCat.hom_ext
  exact QuotSMulTop.equivQuotTensor_naturality r f.hom

def cochainScalarQuotient (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((moduleScalarQuotientFunctor r).mapHomologicalComplex (.up ℕ)).obj C

def cochainScalarQuotientProjection (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    C ⟶ cochainScalarQuotient C r where
  f q := ModuleCat.ofHom (Submodule.mkQ (r • (⊤ : Submodule R (C.X q))))
  comm' i j _hij := by
    apply ModuleCat.hom_ext
    exact (QuotSMulTop.map_comp_mkQ r (C.d i j).hom).symm

def cochainScalarQuotientSequence (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (r • 𝟙 C) (cochainScalarQuotientProjection C r) (by
    apply HomologicalComplex.Hom.ext
    funext q
    exact (RegularCategory.ModuleCat.smulShortComplex (C.X q) r).zero)

theorem cochainScalarQuotientSequence_shortExact
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hreg : ∀ q, IsSMulRegular (C.X q) r) : (cochainScalarQuotientSequence C r).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact _
  intro q
  exact RegularCategory.IsSMulRegular.smulShortComplex_shortExact (M := C.X q) (hreg q)

def cochainScalarQuotientTensorIso (C : CochainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    cochainScalarQuotient C r ≅ Module.TensorFunctor.ModuleTensorFunctor.complex (R ⧸ Ideal.span {r}) C :=
  (NatIso.mapHomologicalComplex (moduleScalarQuotientTensorIso r) (.up ℕ)).app C

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.QuotientComplex
