import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCechDuality

/-! # Injective Cech Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCechExact.CrystallineInjectiveCechExact

noncomputable section

/-!
# Čech acyclicity of native injective sheaves

Positive exactness of the native free Čech sheaves and injectivity give
exactness of their dual cochains. The checked duality isomorphism carries
this to the actual native Čech complex. Forgetting module scalars retains
the same elements and maps, so the conclusion holds in native Witt modules.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.AlgebraicTopology

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "M" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeCechDuality.CrystallineFreeCechDuality.rankOne p k

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

theorem hom_exactAt (I : Sheaf J V) [Injective I] (n : ℕ) :
    (SimplicialInjective.SimplicialInjectiveHom.complex (InjectiveCechDuality.CrystallineInjectiveCechDuality.sheafSimplicial p k X Q s) I).ExactAt
      (n + 1) :=
  SimplicialInjective.SimplicialInjectiveHom.exactAt _ I n
    ((FreeCechExact.CrystallineFreeCechExact.sheaf_exactAt p k X Q s M (n + 1) (Nat.succ_ne_zero n)).of_iso
      (InjectiveCechDuality.CrystallineInjectiveCechDuality.sheafChainIso p k X Q s))

theorem exactAt (I : Sheaf J V) [Injective I] (n : ℕ) (hn : n ≠ 0) :
    ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj I).ExactAt n := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    have hc := (hom_exactAt p k X Q s I n).of_iso
      (InjectiveCechDuality.CrystallineInjectiveCechDuality.complexIso p k X Q s I)
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
    rw [ShortComplex.moduleCat_exact_iff]
    have hd := (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mp hc
    exact (ShortComplex.ab_exact_iff _).mp hd

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCechExact.CrystallineInjectiveCechExact
