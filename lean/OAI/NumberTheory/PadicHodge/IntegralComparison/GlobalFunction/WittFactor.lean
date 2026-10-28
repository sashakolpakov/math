import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionWitt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

/-! # Witt Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFactor

noncomputable section

/-! The canonical map to the spectrum of actual global functions factors the original Witt structure map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X

def affinization : X.left ⟶ Spec (CommRingCat.of A) := X.left.toSpecΓ

theorem affinization_overBase :
    affinization k X ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = X.hom := by
  have h : CommRingCat.ofHom (algebraMap k A) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Projective.GlobalFunctionsFinite.base_value k X r
  have h₁ := congrArg (fun a : CommRingCat.of k ⟶ Γ(X.left, ⊤) => X.left.toSpecΓ ≫ Spec.map a) h
  have h₂ : X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop) =
      X.hom := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  exact h₁.trans h₂

variable (p : ℕ) [Fact p.Prime]

def factor : X.left ⟶ Spec (CommRingCat.of (WittVector p A)) :=
  affinization k X ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : WittVector p A →+* A))

theorem reduction_base :
    (WittVector.constantCoeff : WittVector p A →+* A).comp
      (algebraMap (WittVector p k) (WittVector p A)) =
        (algebraMap k A).comp (WittVector.constantCoeff : WittVector p k →+* k) := rfl

theorem overBase : factor k X p ≫
    Spec.map (CommRingCat.ofHom (algebraMap (WittVector p k) (WittVector p A))) =
      Witt.Crystalline.wittStructureMap p k X := by
  change (affinization k X ≫ Spec.map (CommRingCat.ofHom
      (WittVector.constantCoeff : WittVector p A →+* A))) ≫ _ = _
  rw [Category.assoc, ← Spec.map_comp]
  change affinization k X ≫ Spec.map (CommRingCat.ofHom
    ((WittVector.constantCoeff : WittVector p A →+* A).comp
      (algebraMap (WittVector p k) (WittVector p A)))) = _
  rw [reduction_base]
  change affinization k X ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : WittVector p k →+* k) ≫
    CommRingCat.ofHom (algebraMap k A)) = _
  rw [Spec.map_comp, ← Category.assoc, affinization_overBase]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFactor
