import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFactor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineFrobenius

/-! # Witt Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFrobenius

noncomputable section

/-! The actual scheme q-Frobenius commutes with the canonical global-function Witt factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X

def functions : A →ₐ[k] A := FiniteField.frobeniusAlgHom k A

def witt : WittVector p A →ₐ[WittVector p k] WittVector p A :=
  PeriodInvariants.WittAlgebraFunctor.map p k (functions k X)

omit [CharP k p] in
theorem reduction :
    (WittVector.constantCoeff : WittVector p A →+* A).comp (witt p k X).toRingHom =
      (functions k X).toRingHom.comp WittVector.constantCoeff := rfl

variable (a : ℕ) (hcard : Fintype.card k = p ^ a)

include hcard in
theorem appTop : (BigCrystallineFrobenius.schemeFrobenius p k X a).appTop =
    CommRingCat.ofHom (functions k X).toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (Global.FrobeniusGeometry.iterate p (Fact.out : p.Prime) X.left
    (Global.FrobeniusGeometry.scheme_prime_zero p k X.hom) a).appTop s = s ^ Fintype.card k
  exact (Global.FrobeniusGeometry.iterate_appTop p (Fact.out : p.Prime) X.left
    (Global.FrobeniusGeometry.scheme_prime_zero p k X.hom) a s).trans (congrArg (fun n => s ^ n) hcard.symm)

include hcard in
theorem factor : BigCrystallineFrobenius.schemeFrobenius p k X a ≫ WittFactor.factor k X p =
    WittFactor.factor k X p ≫ Spec.map (CommRingCat.ofHom (witt p k X).toRingHom) := by
  let F := BigCrystallineFrobenius.schemeFrobenius p k X a
  let c : CommRingCat.of (WittVector p A) ⟶ Γ(X.left, ⊤) := CommRingCat.ofHom WittVector.constantCoeff
  let b : Γ(X.left, ⊤) ⟶ Γ(X.left, ⊤) := CommRingCat.ofHom (functions k X).toRingHom
  let w : CommRingCat.of (WittVector p A) ⟶ CommRingCat.of (WittVector p A) :=
    CommRingCat.ofHom (witt p k X).toRingHom
  have hc : w ≫ c = c ≫ b := rfl
  have hn : F ≫ X.left.toSpecΓ = X.left.toSpecΓ ≫ Spec.map b :=
    (Scheme.toSpecΓ_naturality F).trans
      (congrArg (fun t => X.left.toSpecΓ ≫ Spec.map t) (WittFrobenius.appTop p k X a hcard))
  change F ≫ (X.left.toSpecΓ ≫ Spec.map c) = (X.left.toSpecΓ ≫ Spec.map c) ≫ Spec.map w
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ Spec.map c) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => X.left.toSpecΓ ≫ t) (Spec.map_comp c b).symm).trans
          ((congrArg (fun t => X.left.toSpecΓ ≫ Spec.map t) hc.symm).trans
            ((congrArg (fun t => X.left.toSpecΓ ≫ t) (Spec.map_comp w c)).trans
              (Category.assoc _ _ _).symm)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFrobenius
