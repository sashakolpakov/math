import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SourcePairingFormula

/-! # Perfect Split Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectSplitPairing.Construction

noncomputable section

/-!
The native product decomposition supplies the idempotence equations.
Thus a perfect source pairing has perfect literal conjugate-block
restrictions whenever the original projectors are adjoint.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u v

variable {S : Scheme.{u}} {T : Over S} [GrpObj T] [IsCommMonObj T]
  {I : Type v} [Fintype I]

theorem schemeProjector_idempotent (p : I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
    (horth : ∀ i j, i ≠ j → p i ≫ p j = 1) (hcomplete : (∏ i, p i) = 𝟙 T) (i : I) :
    p i ≫ p i = p i := by
  let c := Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete T (𝟙 T) i
  have hc : c ≫ BlockGroups.Construction.fixedPointInclusion (p i) = p i :=
    (Torsion.Decomposition.Construction.schemeProjectorPointEquiv_inclusion p horth hcomplete T (𝟙 T) i).trans (Category.id_comp _)
  calc
    p i ≫ p i = (c ≫ BlockGroups.Construction.fixedPointInclusion (p i)) ≫ p i :=
      congrArg (fun z => z ≫ p i) hc.symm
    _ = c ≫ BlockGroups.Construction.fixedPointInclusion (p i) := by rw [Category.assoc, BlockGroups.Construction.fixedPointInclusion_fixed]
    _ = p i := hc

theorem sourceBlockPairing_isPerfect
    (p : I ⊕ I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
    (horth : ∀ i j, i ≠ j → p i ≫ p j = 1) (hcomplete : (∏ i, p i) = 𝟙 T)
    (b : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (hb : b.toSheafPairing.IsPerfect)
    (hadjoint : ∀ (i : I ⊕ I) (X : Over S) (x y : X ⟶ T),
      b.pairValue (x ≫ p i) y = b.pairValue x (y ≫ p (Sum.swap i))) (i : I) :
    (SourcePairingFormula.Construction.sourceBlockPairing p b i).toSheafPairing.IsPerfect :=
  PerfectBlocks.Construction.fixedPointPairing_isPerfect b hb (p (.inl i)) (p (.inr i))
    (schemeProjector_idempotent p horth hcomplete (.inl i))
    (schemeProjector_idempotent p horth hcomplete (.inr i)) (hadjoint (.inl i))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectSplitPairing.Construction
