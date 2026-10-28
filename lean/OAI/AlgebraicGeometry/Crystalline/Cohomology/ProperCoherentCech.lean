import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ModuleCoefficientPresheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction

/-! # Proper Coherent Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness

noncomputable section

/-! # Coefficient-linear Cech finiteness for proper coherent scheme modules -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (M : X.left.Modules) {ι : Type u} (U : ι → X.left.Opens)

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).obj
    ((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves R X).obj M.val)

def complexIso :
    ((Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.coefficients R).mapHomologicalComplex (.up ℕ)).obj
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U) ≅ complex R X M U :=
  Cech.CoefficientChange.CechCoefficientChange.complexIso (Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.coefficients R)
    (FormalCoproduct.mk ι U).cech (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf X.hom M) ≪≫
      (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapIso
        (Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.iso R X M)

def homologyIso (n : ℕ) :
    (complex R X M U).homology n ≅
      (Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.coefficients R).obj
        ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n) :=
  (HomologicalComplex.homologyMapIso (complexIso R X M U) n).symm ≪≫
    ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).sc n).mapHomologyIso
      (Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.coefficients R)

variable [IsNoetherianRing R] [IsProper X.hom] [M.IsQuasicoherent] [M.IsFiniteType]
  (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))

include hU hUaff in
theorem base_finite (n : ℕ) :
    Module.Finite Γ(Spec (CommRingCat.of R), ⊤)
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n) := by
  let : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    infer_instance
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule X.hom M n
  let : Module.Finite Γ(Spec (CommRingCat.of R), ⊤) (SheafCohomology.AffineH.Projective.H M n) :=
    ProperCoherentCoefficient.ProperCoherentFiniteness.base R X.hom M n
  exact Module.Finite.equiv
    (SheafCohomology.Projective.BaseCechAllDegrees.baseCechHomologyAffineHLinearEquiv X.hom M U hU hUaff n).symm

include hU hUaff in
theorem finite (n : ℕ) : Module.Finite R ((complex R X M U).homology n) := by
  let : Module.Finite Γ(Spec (CommRingCat.of R), ⊤)
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n) := base_finite R X M U hU hUaff n
  have hf : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  let : Module.Finite R ((Base.ModuleCoefficientPresheaf.BaseModuleCoefficientPresheaf.coefficients R).obj
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n)) :=
    NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction.finite _ hf ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n)
  exact Module.Finite.equiv (homologyIso R X M U n).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCech.ProperCoherentCechFiniteness
