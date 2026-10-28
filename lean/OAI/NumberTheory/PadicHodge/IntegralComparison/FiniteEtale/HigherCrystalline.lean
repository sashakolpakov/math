import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.BoundedFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RestrictionJointKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FiniteLevelKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Higher Crystalline -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.HigherCrystalline

noncomputable section

/-! All positive-degree original crystalline cohomology of a finite étale algebra over a finite field vanishes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [Fintype k] [CommRing A] [Algebra k A]
  [CharP k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

local notation "W" => WittVector p k
local notation "X" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k A
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.Cohomology (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f

local instance : IsSeparated (Crystalline.Presentation.affineScheme k A).hom := by
  exact inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k A))))

theorem big_eq_zero (i : ℕ) (z : H (i + 1)) : z = 0 := by
  let (n : ℕ) : Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) :=
    BoundedFiniteness.finite p k A n i
  let : Mono (HomologicalComplex.homologyMap
      (Crystalline.ResolutionComplexExact.sequence (p := p)
        (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f).f (i + 1)) :=
    Crystalline.FiniteLevelKernel.inclusion_mono_succ f i
  apply Crystalline.RestrictionJointKernel.zero_of_restrictions f (i + 1) z
  intro n
  let := BoundedCrystalline.vanishing p k A n i
  exact Subsingleton.elim _ _

theorem integral (i : ℕ) : Subsingleton (Witt.Crystalline.integralCohomology p k X (i + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro z
  let e := Global.Crystalline.Comparison.integralEquivWitt p k X (i + 1)
  exact (e.apply_symm_apply z).symm.trans
    ((congrArg e (big_eq_zero p k A i (e.symm z))).trans e.map_zero)

theorem rational (i : ℕ) : Subsingleton (Witt.Crystalline.rationalCohomology p k X (i + 1)) := by
  let := integral p k A i
  exact inferInstanceAs (Subsingleton (TensorProduct W (FractionRing W)
    (Witt.Crystalline.integralCohomology p k X (i + 1))))

theorem finite (i : ℕ) :
    FiniteDimensional (FractionRing W) (Witt.Crystalline.rationalCohomology p k X (i + 1)) := by
  let := rational p k A i
  infer_instance

theorem charpoly (i : ℕ)
    (F : Module.End (FractionRing W) (Witt.Crystalline.rationalCohomology p k X (i + 1))) :
    letI := finite p k A i
    F.charpoly = 1 := by
  let := rational p k A i
  have h : F = 0 := Subsingleton.elim _ _
  rw [h, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.HigherCrystalline
