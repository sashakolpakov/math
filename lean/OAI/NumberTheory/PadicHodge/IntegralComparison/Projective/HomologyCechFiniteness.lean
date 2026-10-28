import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomologyPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechTotalForget
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Homology Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.HomologyCechFiniteness

noncomputable section

/-! Actual base-ring Cech cohomology of a coherent scheme module over a finite field is finite. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))
  (M : X.left.Modules) {ι : Type u} (U : ι → X.left.Opens)

def complex : CochainComplex (ModuleCat.{u} k) ℕ :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).obj
    ((Affine.HomologyPresheaf.functor k X).obj M)

def abComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).obj
    ((BaseCechTotalForget.presheaves (X := X.left)).obj M)

def forgetIso :
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj (complex k X M U) ≅
      abComplex k X M U :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})
    (FormalCoproduct.mk ι U).cech ((Affine.HomologyPresheaf.functor k X).obj M)

def baseIso :
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k))).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U) ≅ abComplex k X M U :=
  AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso X.hom M U

def homologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).obj ((complex k X M U).homology n) ≅
      (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k))).obj
        ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n) :=
  (((complex k X M U).sc n).mapHomologyIso (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})).symm ≪≫
    HomologicalComplex.homologyMapIso (forgetIso k X M U) n ≪≫
      (HomologicalComplex.homologyMapIso (baseIso k X M U) n).symm ≪≫
        ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).sc n).mapHomologyIso
          (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k)))

theorem finite [IsSeparated X.hom] (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)
    [M.IsQuasicoherent] [M.IsFiniteType] (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    Module.Finite k ((complex k X M U).homology n) := by
  let : Finite Γ(Spec (CommRingCat.of k), ⊤) := Finite.of_equiv k
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.toEquiv
  let : Module.Finite Γ(Spec (CommRingCat.of k), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n) :=
    CechFiniteness.finite k X.hom hprojective M U hU hUaff n
  let : Finite ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n) :=
    Module.finite_of_finite Γ(Spec (CommRingCat.of k), ⊤)
  let : Finite ((complex k X M U).homology n) := Finite.of_equiv
    ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex X.hom M U).homology n)
      (homologyIso k X M U n).symm.addCommGroupIsoToAddEquiv.toEquiv
  exact Module.Finite.of_finite

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.HomologyCechFiniteness
