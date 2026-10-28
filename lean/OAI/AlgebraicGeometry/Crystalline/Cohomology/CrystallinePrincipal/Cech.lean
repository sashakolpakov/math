import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.FormsFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange

/-! # Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech

noncomputable section

/-!
# Affine Čech exactness for the native principal-frame diagram

The natural section equivalences compare the full principal-frame Čech
complex with the actual associated-module Čech complex on the ambient
affine scheme. Consequently native frame cochains are exact in positive
Čech degrees for every finite unit-ideal principal cover.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

def family {R : Type u} [CommRing R] {ι : Type u} (s : ι → R) : ι → PrincipalCoefficient.PrincipalCoefficientCategory.Object R :=
  fun i => ⟨s i⟩

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)
  {ι : Type u} [Finite ι] (s : ι → Q.thickening.ring)

local notation "QR" => Q.thickening.ring

def complex : CochainComplex (ModuleCat.{u} QR) ℕ :=
  (cechComplexFunctor (family s)).obj (FormsFunctor.CrystallinePrincipalFormsFunctor.functor p k B σ a Q n)

def complexIso : complex p k B σ a Q n s ≅
    (Cech.Descent.CechDescent.cechFunctor QR (Affine.Cech.AffineCech.model QR)
      (fun i => Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR (s i))).obj
        (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.associatedSheaf p k B σ Q n).obj :=
  (cechComplexFunctor (family s)).mapIso (FormsFunctor.CrystallinePrincipalFormsFunctor.sectionsIso p k B σ a Q n) ≪≫
    Cech.BaseChange.CechBaseChange.complexIso (PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor QR) (family s)
      (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.associatedSheaf p k B σ Q n).obj

theorem exactAt (hs : Ideal.span (Set.range s) = ⊤) (j : ℕ) (hj : j ≠ 0) :
    (complex p k B σ a Q n s).ExactAt j := by
  let P := (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.associatedSheaf p k B σ Q n).obj
  let U := fun i => Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR (s i)
  let α := Cech.Descent.CechDescent.augmentation QR (Affine.Cech.AffineCech.model QR) U P
  have hα : QuasiIso α := Affine.Cech.AffineCech.tilde_quasiIso QR s
    (CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms.module p k B σ Q n) hs
  have hzero : ((CochainComplex.single₀ (ModuleCat.{u} QR)).obj (P.obj (op ⊤))).ExactAt j :=
    HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (P.obj (op ⊤)) j hj)
  have hd := (quasiIsoAt_iff_exactAt α j hzero).mp (hα.quasiIsoAt j)
  exact hd.of_iso (complexIso p k B σ a Q n s).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech
