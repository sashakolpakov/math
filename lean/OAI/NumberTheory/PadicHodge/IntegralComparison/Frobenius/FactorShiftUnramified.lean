import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.ShiftUnramified

/-! # Factor Shift Unramified -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FactorShiftUnramified

noncomputable section

/-! Prime-to-characteristic shifts of any endomorphism factoring
through Frobenius are formally unramified on the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable (k : Type u) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

theorem shift_hom (r : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom =
      (𝟙 A : A ⟶ A) ^ n / (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A ≫ r.toMul.hom.hom) := by
  have hn : (n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom = (𝟙 A : A ⟶ A) ^ n := by
    calc
      _ = (n • (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)).toMul.hom.hom :=
        congrArg (fun z : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A => z.toMul.hom.hom) (nsmul_one n).symm
      _ = (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom ^ n := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.algebraicEnd_nsmul_hom A n 1
      _ = _ := rfl
  change ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul / (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul).hom.hom = _
  rw [Grp.Hom.hom_hom_div, hn, AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicEnd_mul_apply]
  rfl

theorem formallyUnramified (r : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) (hn : (n : k) ≠ 0) :
    FormallyUnramified ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom.left := by
  let g := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom
  apply AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalUnramified.LocalUnramifiedCriterion.of_local_hom_ext
  intro C hC J hJ a b hred hshift
  let s := a ≫ A.hom
  have hb : b ≫ A.hom = s := by
    have h := congrArg (fun z => z ≫ A.hom) hshift
    simpa only [Category.assoc, Over.w] using h.symm
  let α : Over.mk s ⟶ A := Over.homMk a rfl
  let β : Over.mk s ⟶ A := Over.homMk b hb
  let κ : k →+* C := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop ≫
    (Scheme.ΓSpecIso C).hom).hom
  have hF : α ≫ AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A = β ≫ AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A := by
    apply Over.OverMorphism.ext
    exact Infinitesimal.equal_after_frobenius_of_reduction k C κ J hJ
      A.left (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.varietyBaseMap k A) a b hred
  have hr : α ≫ (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A ≫ r.toMul.hom.hom) =
      β ≫ (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A ≫ r.toMul.hom.hom) := by
    rw [← Category.assoc, ← Category.assoc, hF]
  have hg : α ≫ g = β ≫ g := Over.OverMorphism.ext hshift
  change α ≫ ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom =
    β ≫ ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom at hg
  rw [shift_hom, GrpObj.comp_div, GrpObj.comp_div, MonObj.comp_pow, MonObj.comp_pow,
    Category.comp_id, Category.comp_id, hr] at hg
  have hp : α ^ n = β ^ n := div_left_inj.mp hg
  have hred' : AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower.reduction s J A α = AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower.reduction s J A β :=
    Over.OverMorphism.ext hred
  have hu : IsUnit (n : C) := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power.PowerGeometry.unit_on_local_test n
    (AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.field_natCast_stalk_isUnit n hn) s
  exact congrArg (fun z : Over.mk s ⟶ A => z.left)
    (AlgebraicGeometry.AbelianScheme.TorsionQuotient.LocalPowerIn.LocalPower.power_lift_unique s J hJ A n hu α β hred' hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FactorShiftUnramified
