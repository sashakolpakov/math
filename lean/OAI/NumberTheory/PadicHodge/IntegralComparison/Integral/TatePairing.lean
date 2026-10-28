import OAI.NumberTheory.PadicHodge.IntegralComparison.TateCompatibleCharacters
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PairingTransition
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection

/-! # Tate Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TatePairing

noncomputable section

/-! The finite multiplication-cover characters construct an injective
pairing of actual integral H¹ with the actual geometric Tate module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

def torsionEquiv (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) n ≃+ Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n)) where
  toFun t := Additive.ofMul ⟨t.val.toMul, congrArg Additive.toMul t.property⟩
  invFun t := ⟨Additive.ofMul t.toMul.val, congrArg Additive.ofMul t.toMul.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [IsAlgClosed k] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem torsionEquiv_transition (n : ℕ) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) (n + 1)) :
    torsionEquiv ℓ A n (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n t) =
      Additive.ofMul (MultiplicationCoverRefinement.pointMap ℓ n A
        (torsionEquiv ℓ A (n + 1) t).toMul) := rfl

def finiteCharacter (n : ℕ) (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) n →+ ZMod (ℓ ^ n) :=
  (TorsionPointCharacter.character ℓ n A hℓ x).comp (torsionEquiv ℓ A n).toAddMonoidHom

theorem finiteCharacter_transition (n : ℕ)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ (n + 1) A.left).H 1)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) (n + 1)) :
    finiteCharacter ℓ A hℓ n
      (Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1 x)
        (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n t) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
        (finiteCharacter ℓ A hℓ (n + 1) x t) :=
  Finite.PairingTransition.transition ℓ n A hℓ x (torsionEquiv ℓ A (n + 1) t).toMul

theorem finiteCharacter_injective (n : ℕ) : Function.Injective (finiteCharacter ℓ A hℓ n) := by
  intro x y h
  apply TorsionPointCharacter.character_injective ℓ n A hℓ
  apply AddMonoidHom.ext
  intro t
  obtain ⟨s, rfl⟩ := (torsionEquiv ℓ A n).surjective t
  exact congrArg (fun f : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Geometric.TateModule.Points A) n →+ ZMod (ℓ ^ n) => f s) h

def integralFamily : A.left.EllAdicCohomology ℓ 1 →+
    TateCompatibleCharacters.compatible (H := Geometric.TateModule.Points A) ℓ where
  toFun x := ⟨fun n => finiteCharacter ℓ A hℓ n (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 x), by
    intro n t
    have he : Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1
        (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ (n + 1) A.left 1 x) =
        AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 x := by
      change Sheaf.H.map _ 1 (Sheaf.H.map _ 1 x) = Sheaf.H.map _ 1 x
      rw [← Sheaf.H.map_comp_apply, AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicReduction_transition]
    dsimp only
    rw [← he]
    exact finiteCharacter_transition ℓ A hℓ n _ t⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    apply AddMonoidHom.ext
    intro t
    change TorsionPointCharacter.character ℓ n A hℓ
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 0) _ = 0
    rw [map_zero, map_zero]
    rfl
  map_add' x y := by
    apply Subtype.ext
    funext n
    apply AddMonoidHom.ext
    intro t
    change TorsionPointCharacter.character ℓ n A hℓ
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 (x + y)) _ = _
    rw [map_add, map_add]
    rfl

def pairing : A.left.EllAdicCohomology ℓ 1 →+
    Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) :=
  (TateCompatibleCharacters.toDual ℓ).comp (integralFamily ℓ A hℓ)

theorem pairing_reduction (x : A.left.EllAdicCohomology ℓ 1)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) (n : ℕ) :
    PadicInt.toZModPow n (pairing ℓ A hℓ x t) =
      finiteCharacter ℓ A hℓ n (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 x) (t.val n) :=
  TateCompatibleCharacters.value_reduction ℓ _ _ n

theorem pairing_injective : Function.Injective (pairing ℓ A hℓ) := by
  intro x y h
  have he := TateCompatibleCharacters.toDual_injective ℓ (Geometric.TateModule.divisible A ℓ hℓ) h
  apply AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction.integralEllAdicH1_ext_finiteReduction ℓ A.left
  intro n
  apply finiteCharacter_injective ℓ A hℓ n
  exact congrArg (fun f : TateCompatibleCharacters.compatible (H := Geometric.TateModule.Points A) ℓ => f.val n) he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TatePairing
