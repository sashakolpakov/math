import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeValues
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension

/-! # Pairing Reflection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PairingReflection

noncomputable section

/-! Alternation descends along the actual faithfully flat field
extension, including for points over arbitrary parameter schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

universe u

variable {k K : Type u} [Field k] [Field K] (s : Spec (.of K) ⟶ Spec (.of k))
  (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
  (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := G.X) (B := G.X)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))

theorem alternating_of_field_pullback
    (h : ∀ (T : Over (Spec (.of K))) (x : T ⟶ ((Over.pullback s).mapGrp.obj G).X),
      (AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback s G G e).pairValue x x = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ G.X) : e.pairValue x x = 1 := by
  have : Flat s := Picard.PoincareBundle.Field.Extension.flat s
  have : Surjective s := Picard.PoincareBundle.Field.Extension.surjective s
  have : IsAffineHom s := isAffineHom_of_isAffine _
  let U := (Over.pullback s).obj T
  let p : (Over.map s).obj U ⟶ T := Over.homMk (pullback.fst T.hom s) pullback.condition
  have : Epi p.left := inferInstanceAs (Epi (pullback.fst T.hom s))
  have : Epi p := Over.epi_of_epi_left p
  have hx : (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G U).symm ((Over.pullback s).map x) = p ≫ x := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have he := (AbelianScheme.IsogenyQuotient.PairingBaseChangeValues.Construction.nativePairingPullback_eq_one_iff s G G e U
    ((Over.pullback s).map x) ((Over.pullback s).map x)).mp
      (h U ((Over.pullback s).map x))
  rw [hx] at he
  apply (cancel_epi p).mp
  exact (e.pairValue_natural p x x).symm.trans (he.trans (MonObj.comp_one p).symm)

theorem torsion_alternating_of_field_pullback (n : ℕ)
    (b : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
    (h : ∀ (T : Over (Spec (.of K)))
      (x : T ⟶ (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup ((Over.pullback s).mapGrp.obj G) n).X),
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback s G G n b).pairValue x x = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n) : b.pairValue x x = 1 := by
  apply alternating_of_field_pullback s (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) b _ T x
  intro U y
  have hi : (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso s G n).hom.hom.hom ≫
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso s G n).inv.hom.hom = 𝟙 _ :=
    congrArg (fun a => (Grp.forget (Over (Spec (.of K)))).map a)
      (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso s G n).hom_inv_id
  have hy := h U (y ≫ (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso s G n).hom.hom.hom)
  simpa only [AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue,
    Category.assoc, hi, Category.comp_id] using hy

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PairingReflection
