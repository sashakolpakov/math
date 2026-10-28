import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension

/-! # Field Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldAlternation.Construction

noncomputable section

/-! Faithfully flat scalar extension detects alternation on every test
scheme over the original field, including nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem fieldNativePolarizationPairing_alternating_original
    {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
    (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of k)))
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let F := Over.pullback s
  let U := F.obj T
  let p : (Over.map s).obj U ⟶ T := (Over.mapPullbackAdj s).counit.app T
  have : Flat s := Picard.PoincareBundle.Field.Extension.flat s
  have : Surjective s := Picard.PoincareBundle.Field.Extension.surjective s
  have : IsAffineHom s := isAffineHom_of_isAffine _
  have : Epi p.left := inferInstanceAs (Epi (pullback.fst T.hom s))
  have : Epi p := Over.epi_of_epi_left p
  let z : U ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n :=
    F.map x ≫ (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s (Grp.mk A.scheme) n).hom
  have hz : Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n U z = p ≫ x := by
    unfold Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint
    change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.scheme) n) U).symm
      ((F.map x ≫ (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s (Grp.mk A.scheme) n).hom) ≫
        (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s (Grp.mk A.scheme) n).inv) = p ≫ x
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply Over.OverMorphism.ext
    change (F.map x).left ≫ pullback.fst (Torsion.Groups.Construction.nativeTorsionScheme A.scheme n).hom s =
      pullback.fst T.hom s ≫ x.left
    simp only [F, Over.pullback_map_left, pullback.lift_fst]
  have h := IsogenyQuotient.Field.CanonicalPairingBaseChange.Construction.fieldNativePolarizationPairing_baseChange_value D pol n hn s U z z
  rw [IsogenyQuotient.Field.PolarizationAlternating.Construction.fieldNativePolarizationPairing_alternating, hz] at h
  have hv : (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue (p ≫ x) (p ≫ x) = 1 := by
    apply (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s U).injective
    exact h.symm.trans (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s U).map_one.symm
  rw [Annihilator.Construction.SchemeBicharacter.pairValue_natural] at hv
  exact (cancel_epi p).mp (hv.trans (MonObj.comp_one p).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldAlternation.Construction
