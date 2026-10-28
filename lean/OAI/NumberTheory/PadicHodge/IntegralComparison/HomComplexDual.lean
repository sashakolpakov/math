import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.DualPurity
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Limits

/-! # Hom Complex Dual -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomComplexDual.Comparison

noncomputable section

/-! The ordinary Hom complex into the coefficient ring is the genuine
coefficient-dual complex. This also transports purity to any specified
rank-one trivialization of the target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

def functorIso : preadditiveYoneda.obj (ModuleCat.of R R) ≅
    ExactModuleDualFunctor.functor R ⋙ forget₂ (ModuleCat R) AddCommGrpCat :=
  NatIso.ofComponents
    (fun M => (ModuleCat.homAddEquiv (M := M.unop) (N := ModuleCat.of R R)).toAddCommGrpIso) (by
      intro M N f
      ext q
      rfl)

variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def complexIso :
    (((preadditiveYoneda.obj (ModuleCat.of R R)).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op) ≅
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj (DualComplexHomology.complex R P)) :=
  (NatIso.mapHomologicalComplex (functorIso R) (ComplexShape.down ℕ).symm).app P.op

def homologyIso (n : ℕ) :
    ((((preadditiveYoneda.obj (ModuleCat.of R R)).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op).homology n) ≅
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((DualComplexHomology.complex R P).homology n) :=
  HomologicalComplex.homologyMapIso (complexIso R P) n ≪≫
    ((DualComplexHomology.complex R P).sc n).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)

def targetHomologyIso (N : ModuleCat.{u} R) (e : N ≅ ModuleCat.of R R) (n : ℕ) :
    ((((preadditiveYoneda.obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.op).homology n) ≅
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((DualComplexHomology.complex R P).homology n) :=
  HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (preadditiveYoneda.mapIso e) (ComplexShape.down ℕ).symm).app P.op) n ≪≫
      homologyIso R P n

variable (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
  (Q : ProjectiveResolution (IntegralComparison.ProjectiveResolution.DualPurity.quotient R rs))
  (N : ModuleCat.{u} R) (e : N ≅ ModuleCat.of R R)

def purityIso :
    ((((preadditiveYoneda.obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj Q.complex.op).homology rs.length) ≅
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (IntegralComparison.ProjectiveResolution.DualPurity.quotient R rs) :=
  targetHomologyIso R Q.complex N e rs.length ≪≫
    (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      (IntegralComparison.ProjectiveResolution.DualPurity.homologyIso R rs hreg Q)

include hreg e in
theorem exactAt (n : ℕ) (hn : n ≠ rs.length) :
    (((preadditiveYoneda.obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj Q.complex.op).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (targetHomologyIso R Q.complex N e n).isZero_iff.mpr
  exact (forget₂ (ModuleCat R) AddCommGrpCat).map_isZero
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (IntegralComparison.ProjectiveResolution.DualPurity.exactAt R rs hreg Q n hn))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomComplexDual.Comparison
