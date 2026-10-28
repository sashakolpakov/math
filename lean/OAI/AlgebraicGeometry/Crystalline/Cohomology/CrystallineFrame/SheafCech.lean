import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FormsSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.SheafCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittCech

/-! # Sheaf Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech.CrystallineFrameSheafCech

noncomputable section

/-!
# Čech exactness for terms of the actual native sheaf resolution

The native frame-form presheaves are already sheaves. Their canonical
section identifications after coefficient lifting identify the actual
sheaf Čech complexes with the previously computed Witt-linear cochains.
Thus every term of the native sheaf resolution has vanishing positive
Čech cohomology on every finite unit-ideal principal cover.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

local instance coefficientLimits : PreservesLimitsOfSize.{u, u} E := by
  unfold PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift
  have : PreservesLimitsOfSize.{u, u} (ModuleCat.uliftFunctor.{u + 1, u} W) := inferInstance
  have : PreservesLimitsOfSize.{u, u}
      (ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : Site.CoefficientRing p k ≃+* W).toRingHom) :=
    ⟨fun {J'} [_] => ⟨fun {K'} => ModuleCat.preservesLimit_restrictScalars _ K'⟩⟩
  exact comp_preservesLimits _ _

local instance coefficientHomology : (E).PreservesHomology := Functor.preservesHomologyOfExact _

def sectionPresheafIso (n : ℕ) : ((SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n).obj ≅
    (Resolution.CrystallineFrameResolution.complex p k B σ a).X n ⋙ E :=
  CoefficientSheaf.CrystallineCoefficientSheaf.presheafIso p k X _
    (FormsSheaf.CrystallineFrameFormsSheaf.term_isSheaf p k B σ a n)

variable (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)

def principalDiagramIso :
    (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.coefficients p k X Q).obj
      ((SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n) ≅
        CrystallinePrincipal.WittForms.CrystallinePrincipalWittForms.nativeFunctor p k B σ a Q n ⋙ E :=
  Functor.isoWhiskerLeft (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).op
    (sectionPresheafIso p k B σ a n)

variable {ι : Type u} [Finite ι] (s : ι → Q.thickening.ring)

def complex : CochainComplex V ℕ :=
  (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj
    ((SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n)

def complexIso : complex p k B σ a Q n s ≅
    ((E).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CrystallinePrincipal.WittCech.CrystallinePrincipalWittCech.complex p k B σ a Q n s) :=
  (cechComplexFunctor.{u, u, u + 1, u, u + 2} (A := V)
    (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s)).mapIso (principalDiagramIso p k B σ a Q n) ≪≫
      (Cech.CoefficientChange.CechCoefficientChange.complexIso E
        (FormalCoproduct.mk ι (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s)).cech
        (CrystallinePrincipal.WittForms.CrystallinePrincipalWittForms.nativeFunctor p k B σ a Q n)).symm

theorem exactAt (hs : Ideal.span (Set.range s) = ⊤) (j : ℕ) (hj : j ≠ 0) :
    (complex p k B σ a Q n s).ExactAt j := by
  have h : (((E).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CrystallinePrincipal.WittCech.CrystallinePrincipalWittCech.complex p k B σ a Q n s)).ExactAt j :=
    (CrystallinePrincipal.WittCech.CrystallinePrincipalWittCech.exactAt p k B σ a Q n s hs j hj).map E
  exact h.of_iso (complexIso p k B σ a Q n s).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech.CrystallineFrameSheafCech
