import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationBaseChange

/-! # Pairing Base Change Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeValues.Construction

noncomputable section

/-!
The native base-change formula retains literal scheme points. It proves
that annihilation, alternation, and the original adjoint morphism equations
are preserved by arbitrary base change.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (G H : Grp (Over S))
  [IsCommMonObj G.X] [IsCommMonObj H.X]
  (e : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem nativePairingPullback_native_value
    (U : Over T) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X)
    (y : U ⟶ ((Over.pullback f).mapGrp.obj H).X) :
    (PairingBaseChange.Construction.nativePairingPullback f G H e).pairValue x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U
        (e.pairValue ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x) ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H U).symm y)) :=
  congrArg ULift.down (PairingBaseChange.Construction.nativePairingPullback_value f G H e U x y)

theorem nativePairingPullback_eq_one_iff
    (U : Over T) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X)
    (y : U ⟶ ((Over.pullback f).mapGrp.obj H).X) :
    (PairingBaseChange.Construction.nativePairingPullback f G H e).pairValue x y = 1 ↔
      e.pairValue ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x) ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H U).symm y) = 1 := by
  rw [nativePairingPullback_native_value]
  constructor
  · intro h
    apply (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U).injective
    exact h.trans (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U).map_one.symm
  · intro h
    rw [h, map_one]

theorem nativePairingPullback_adjoint
    (p : G ⟶ G) (q : H ⟶ H)
    (hadj : ∀ (V : Over S) (x : V ⟶ G.X) (y : V ⟶ H.X),
      e.pairValue (x ≫ p.hom.hom) y = e.pairValue x (y ≫ q.hom.hom))
    (U : Over T) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X)
    (y : U ⟶ ((Over.pullback f).mapGrp.obj H).X) :
    (PairingBaseChange.Construction.nativePairingPullback f G H e).pairValue (x ≫ ((Over.pullback f).mapGrp.map p).hom.hom) y =
      (PairingBaseChange.Construction.nativePairingPullback f G H e).pairValue x (y ≫ ((Over.pullback f).mapGrp.map q).hom.hom) := by
  rw [nativePairingPullback_native_value, nativePairingPullback_native_value]
  have hx := CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp f p U x
  have hy := CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp f q U y
  exact congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U)
    ((congrArg (fun z : (Over.map f).obj U ⟶ G.X =>
      e.pairValue z ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H U).symm y)) hx).trans
        ((hadj ((Over.map f).obj U) _ _).trans
          (congrArg (fun z : (Over.map f).obj U ⟶ H.X =>
            e.pairValue ((CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x) z) hy.symm)))

omit [IsCommMonObj H.X] in
theorem nativePairingPullback_alternating
    (b : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := G.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (halt : ∀ (V : Over S) (x : V ⟶ G.X), b.pairValue x x = 1)
    (U : Over T) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    (PairingBaseChange.Construction.nativePairingPullback f G G b).pairValue x x = 1 := by
  rw [nativePairingPullback_native_value, halt, map_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeValues.Construction
