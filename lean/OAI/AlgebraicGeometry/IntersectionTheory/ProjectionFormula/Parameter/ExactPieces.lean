import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex

/-! # Exact Pieces -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ExactPieces

noncomputable section

/-! An exact sequence with scalar maps at its ends yields the
short exact sequence from the parameter quotient to the middle term
to the parameter-annihilated submodule. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped Pointwise

universe u

variable (R : Type u) [CommRing R] (r : R) (A B C : ModuleCat.{u} R)
  (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  (hA : Function.Exact (LinearMap.lsmul R A r) f)
  (hB : Function.Exact f g)
  (hC : Function.Exact g (LinearMap.lsmul R C r))

include hA in
theorem kernel_eq : r • (⊤ : Submodule R A) = LinearMap.ker f := by
  rw [LinearMap.exact_iff.mp hA,
    ← LinearMap.exact_iff.mp (LinearMap.exact_lsmul_mkQ_smul_top A r), Submodule.ker_mkQ]

def left : QuotSMulTop r A →ₗ[R] B :=
  (r • (⊤ : Submodule R A)).liftQ f (kernel_eq R r A B f hA).le

def right : B →ₗ[R] LinearMap.ker (LinearMap.lsmul R C r) :=
  g.codRestrict _ (fun b => hC.apply_apply_eq_zero b)

theorem left_injective : Function.Injective (left R r A B f hA) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ f (kernel_eq R r A B f hA)

theorem right_surjective : Function.Surjective (right R r B C g hC) := by
  intro c
  obtain ⟨b, hb⟩ := (hC c.val).mp c.property
  exact ⟨b, Subtype.ext hb⟩

include hB in
theorem exact : Function.Exact (left R r A B f hA) (right R r B C g hC) := by
  intro b
  constructor
  · intro hb
    have hg : g b = 0 := congrArg Subtype.val hb
    obtain ⟨a, ha⟩ := (hB b).mp hg
    exact ⟨Submodule.Quotient.mk a, ha⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (r • (⊤ : Submodule R A)) a
    apply Subtype.ext
    exact hB.apply_apply_eq_zero a

def sequence : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (left R r A B f hA) (right R r B C g hC)
    (ExactPieces.exact R r A B C f g hA hB hC).linearMap_comp_eq_zero

theorem shortExact : (sequence R r A B C f g hA hB hC).ShortExact where
  exact := ModuleCat.shortComplex_exact _ (ExactPieces.exact R r A B C f g hA hB hC)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (left_injective R r A B f hA)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (right_surjective R r B C g hC)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ExactPieces
