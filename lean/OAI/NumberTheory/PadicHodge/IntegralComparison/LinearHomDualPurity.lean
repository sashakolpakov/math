import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.DualPurity
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Linear Hom Dual Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomDualPurity

noncomputable section

/-! The coefficient-dual purity is an isomorphism of modules for the
linear Hom complex, before forgetting the coefficient action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

def functorIso : (linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R) ≅
    ExactModuleDualFunctor.functor R :=
  NatIso.ofComponents
    (fun M => (ModuleCat.homLinearEquiv (R := R) (S := R)
      (M := M.unop) (N := ModuleCat.of R R)).toModuleIso) (by
      intro M N f
      ext q
      rfl)

variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def complexIso :
    ((((linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op) ≅
      DualComplexHomology.complex R P :=
  (NatIso.mapHomologicalComplex (functorIso R) (ComplexShape.down ℕ).symm).app P.op

def homologyIso (n : ℕ) :
    (((((linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op).homology n) ≅
      (DualComplexHomology.complex R P).homology n :=
  HomologicalComplex.homologyMapIso (complexIso R P) n

def targetHomologyIso (N : ModuleCat.{u} R) (e : N ≅ ModuleCat.of R R) (n : ℕ) :
    (((((linearYoneda R (ModuleCat.{u} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op).homology n) ≅
      (DualComplexHomology.complex R P).homology n :=
  HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex ((linearYoneda R (ModuleCat.{u} R)).mapIso e)
      (ComplexShape.down ℕ).symm).app P.op) n ≪≫ homologyIso R P n

variable (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
  (Q : ProjectiveResolution (IntegralComparison.ProjectiveResolution.DualPurity.quotient R rs))
  (N : ModuleCat.{u} R) (e : N ≅ ModuleCat.of R R)

def purityIso :
    (((((linearYoneda R (ModuleCat.{u} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj Q.complex.op).homology rs.length) ≅
      IntegralComparison.ProjectiveResolution.DualPurity.quotient R rs :=
  targetHomologyIso R Q.complex N e rs.length ≪≫
    IntegralComparison.ProjectiveResolution.DualPurity.homologyIso R rs hreg Q

include hreg e in
theorem exactAt (n : ℕ) (hn : n ≠ rs.length) :
    ((((linearYoneda R (ModuleCat.{u} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj Q.complex.op).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (targetHomologyIso R Q.complex N e n).isZero_iff.mpr
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (IntegralComparison.ProjectiveResolution.DualPurity.exactAt R rs hreg Q n hn)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomDualPurity
