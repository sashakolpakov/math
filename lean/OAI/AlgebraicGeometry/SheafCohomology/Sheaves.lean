import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles
import OAI.AlgebraicGeometry.SheafCohomology.Ext
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Sheaves.Projective

noncomputable section

/-!
ProjectiveCohomology constructions on the actual Zariski site. Tensor products are
sheafifications of sectionwise tensor products over the structure sheaf.
Sheaf cohomology is Ext from the constant complex sheaf to the underlying
complex-vector-space sheaf. Neither construction uses Riemann–Roch.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped BigOperators

abbrev LineBundle (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle A.variety.presentation

/-- Constants in the structure sheaf come from the specified complex base. -/
def complexGlobalScalars (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ℂ →+* Γ(A.carrier, ⊤) :=
  A.variety.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom

abbrev ComplexSheaves (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Sheaf (Opens.grothendieckTopology A.carrier) (ModuleCat.{0} ℂ)

/-- Forget an O_A-module to its actual sheaf of complex vector spaces. -/
def complexSheaf (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) :
    ComplexSheaves A :=
  (sheafCompose (Opens.grothendieckTopology A.carrier)
      (ModuleCat.restrictScalars (complexGlobalScalars A))).obj
    ((SheafOfModules.forgetToSheafModuleCat A.carrier.ringCatSheaf
      (op (⊤ : A.carrier.Opens)) (Limits.isTerminalTop.op _)).obj M)

/-- Forgetting the module structure preserves actual sheaf isomorphisms. -/
def complexSheafIso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {M N : A.carrier.Modules} (e : M ≅ N) :
    complexSheaf A M ≅ complexSheaf A N :=
  (sheafCompose (Opens.grothendieckTopology A.carrier)
      (ModuleCat.restrictScalars (complexGlobalScalars A))).mapIso
    ((SheafOfModules.forgetToSheafModuleCat A.carrier.ringCatSheaf
      (op (⊤ : A.carrier.Opens)) (Limits.isTerminalTop.op _)).mapIso e)

/-- The constant complex sheaf, whose Hom functor is global sections. -/
def constantComplexSheaf (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ComplexSheaves A :=
  (constantSheaf (Opens.grothendieckTopology A.carrier) (ModuleCat ℂ)).obj
    (ModuleCat.of ℂ ℂ)

instance complexSheavesHasExt (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    HasExt.{1} (ComplexSheaves A) := HasExt.standard _

/-- Genuine Zariski sheaf cohomology with its induced complex scalar action. -/
abbrev coherentCohomology (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) (i : ℕ) :=
  Abelian.Ext.{1} (constantComplexSheaf A) (complexSheaf A M) i

/-- Degree zero of this construction is the actual space of global sections. -/
def coherentH0EquivSections (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) :
    coherentCohomology A M 0 ≃ Γ(M, ⊤) :=
  Abelian.Ext.homEquiv₀.trans
    (((constantSheafAdj (Opens.grothendieckTopology A.carrier) (ModuleCat ℂ)
      Limits.isTerminalTop).homEquiv _ _).trans
      ((ModuleCat.homLinearEquiv (S := ℂ)).toEquiv.trans
        (LinearMap.ringLmapEquivSelf ℂ ℂ _).toEquiv))

/-- The dimension-bounded alternating sum of coherent cohomology dimensions.
For coherent sheaves on A, cohomology is finite and vanishes above dim A;
the construction itself does not assume either theorem. -/
def coherentEuler (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) : ℤ :=
  ∑ i ∈ Finset.range (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap + 1),
    (-1 : ℤ) ^ i * (Module.finrank ℂ (coherentCohomology A M i) : ℤ)

/-- Isomorphic actual sheaves induce linearly isomorphic cohomology spaces. -/
def coherentCohomologyIso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {M N : A.carrier.Modules}
    (e : M ≅ N) (i : ℕ) : coherentCohomology A M i ≃ₗ[ℂ] coherentCohomology A N i :=
  SheafCohomology.Ext.Projective.extRightIso ℂ (constantComplexSheaf A) (complexSheafIso A e) i

/-- Euler characteristic depends on the sheaf, not its presentation. -/
theorem coherentEuler_eq_of_iso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) {M N : A.carrier.Modules}
    (e : M ≅ N) : coherentEuler A M = coherentEuler A N := by
  unfold coherentEuler
  apply Finset.sum_congr rfl
  intro i _
  rw [(coherentCohomologyIso A e i).finrank_eq]

/-- Tensor product of actual O_A-module sheaves. -/
def sheafTensor (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M N : A.carrier.Modules) :
    A.carrier.Modules :=
  (PresheafOfModules.sheafification (𝟙 A.carrier.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := A.carrier.presheaf) M.val N.val)

/-- Actual tensor powers, as sheaves; the zeroth power is O_A. -/
def tensorPower (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : LineBundle A) : ℕ → A.carrier.Modules
  | 0 => SheafOfModules.unit A.carrier.ringCatSheaf
  | n + 1 => sheafTensor A (tensorPower A L n) L.sheaf

@[simp] theorem tensorPower_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : LineBundle A) :
    Projective.tensorPower A L 0 = SheafOfModules.unit A.carrier.ringCatSheaf := rfl

@[simp] theorem tensorPower_succ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : LineBundle A) (n : ℕ) :
    Projective.tensorPower A L (n + 1) = sheafTensor A (Projective.tensorPower A L n) L.sheaf := rfl

/-- The constructed first tensor power is isomorphic to the original sheaf. -/
def tensorPowerOneIso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : LineBundle A) :
    Projective.tensorPower A L 1 ≅ L.sheaf :=
  (PresheafOfModules.sheafification (𝟙 A.carrier.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.leftUnitor
      (C := PresheafOfModules (A.carrier.presheaf ⋙ forget₂ CommRingCat RingCat))
      L.sheaf.val) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 A.carrier.ringCatSheaf.obj)).counit).app L.sheaf

@[simp] theorem coherentEuler_tensorPower_one (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : LineBundle A) :
    coherentEuler A (Projective.tensorPower A L 1) = coherentEuler A L.sheaf :=
  coherentEuler_eq_of_iso A (tensorPowerOneIso A L)

end

end OAI.AlgebraicGeometry.SheafCohomology.Sheaves.Projective
