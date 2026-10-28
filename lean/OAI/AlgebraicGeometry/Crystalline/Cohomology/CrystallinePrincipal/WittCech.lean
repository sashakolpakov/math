import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Witt Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittCech.CrystallinePrincipalWittCech

noncomputable section

/-!
# Čech exactness for the actual Witt-linear frame resolution

The ambient-ring Čech computation is transported through the checked
identity with the original native Witt-linear frame functor. Restriction
of scalars preserves homology, giving exactness of its actual cochains.
-/

open _root_.CategoryTheory Limits Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)
  {ι : Type u} [Finite ι] (s : ι → Q.thickening.ring)

local notation "W" => WittVector p k

local instance scalars_additive : (WittForms.CrystallinePrincipalWittForms.scalars p k B Q).Additive := by
  dsimp [WittForms.CrystallinePrincipalWittForms.scalars]
  infer_instance

local instance scalars_limits : PreservesLimitsOfSize.{u, u} (WittForms.CrystallinePrincipalWittForms.scalars p k B Q) := by
  dsimp [WittForms.CrystallinePrincipalWittForms.scalars]
  infer_instance

local instance scalars_homology : (WittForms.CrystallinePrincipalWittForms.scalars p k B Q).PreservesHomology :=
  ScalarRestriction.ScalarRestrictionIso.restrictScalars_preservesHomology (algebraMap W Q.thickening.ring)

def complex : CochainComplex (ModuleCat.{u} W) ℕ :=
  (cechComplexFunctor (Cech.CrystallinePrincipalCech.family s)).obj
    (WittForms.CrystallinePrincipalWittForms.nativeFunctor p k B σ a Q n)

def complexIso : complex p k B σ a Q n s ≅
    (((WittForms.CrystallinePrincipalWittForms.scalars p k B Q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Cech.CrystallinePrincipalCech.complex p k B σ a Q n s)) :=
  (cechComplexFunctor (Cech.CrystallinePrincipalCech.family s)).mapIso
    (WittForms.CrystallinePrincipalWittForms.functorIso p k B σ a Q n) ≪≫
  (Cech.CoefficientChange.CechCoefficientChange.complexIso (WittForms.CrystallinePrincipalWittForms.scalars p k B Q)
    (FormalCoproduct.mk ι (Cech.CrystallinePrincipalCech.family s)).cech
    (FormsFunctor.CrystallinePrincipalFormsFunctor.functor p k B σ a Q n)).symm

theorem exactAt (hs : Ideal.span (Set.range s) = ⊤) (j : ℕ) (hj : j ≠ 0) :
    (complex p k B σ a Q n s).ExactAt j := by
  have ht : (((WittForms.CrystallinePrincipalWittForms.scalars p k B Q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Cech.CrystallinePrincipalCech.complex p k B σ a Q n s)).ExactAt j :=
    (Cech.CrystallinePrincipalCech.exactAt p k B σ a Q n s hs j hj).map (WittForms.CrystallinePrincipalWittForms.scalars p k B Q)
  exact ht.of_iso (complexIso p k B σ a Q n s).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.WittCech.CrystallinePrincipalWittCech
