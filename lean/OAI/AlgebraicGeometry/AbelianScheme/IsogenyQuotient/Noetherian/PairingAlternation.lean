import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.MapGeometricDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.PairingTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction

/-! # Pairing Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingAlternation.Construction

noncomputable section

/-! Geometric alternation determines the actual relative pairing:
its values lie in etale roots of unity, even over nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem noetherianNativePolarizationPairing_alternating
    {S : Scheme} [IsLocallyNoetherian S] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
    (n : ℕ) (hn : 0 < n) {k : Type} [Field k] [CharZero k]
    (base : S ⟶ Spec (.of k)) (T : Over S) (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  let H := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n
  let e := PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D pol n hn
  have : Etale (Multiplicative.Construction.rootsOfUnityScheme S n).hom := Multiplicative.Construction.rootsOfUnityScheme_etale S n
    (Unit.Construction.positive_integer_unit_on_characteristic_zero_base base n hn)
  have hd : e.pairValue (𝟙 H) (𝟙 H) = 1 := by
    apply Torsion.MapGeometricDetection.Construction.torsionHom_eq_of_geometric_baseChanges n _ _
      (e.pairValue_pow_eq_one n (Torsion.PairingTarget.Construction.nativeTorsionScheme_identity_killed A.scheme n) H (𝟙 H) (𝟙 H))
      (one_pow n)
    intro K _ _ s
    apply Torsion.MapGeometricDetection.Construction.overHom_baseChange_eq_of_counit
    let F := Over.pullback s
    let U := F.obj H
    let p : (Over.map s).obj U ⟶ H := (Over.mapPullbackAdj s).counit.app H
    let z : U ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n :=
      (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s (Grp.mk A.scheme) n).hom
    have hz : Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n U z = p := by
      unfold Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint
      change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Torsion.SheafComparison.Construction.kernelTorsionGroup (Grp.mk A.scheme) n) U).symm
        ((Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s (Grp.mk A.scheme) n).hom ≫
          (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s (Grp.mk A.scheme) n).inv) = p
      rw [Iso.hom_inv_id]
      apply Over.OverMorphism.ext
      exact Category.id_comp _
    have hv := PairingBaseChange.Construction.noetherianNativePolarizationPairing_baseChange_value D pol n hn s U z z
    have ha : (PolarizationAdapter.Construction.noetherianNativePolarizationPairing (A.pullback s) (D.pullback s)
        (pol.pullback s) n hn).pairValue z z = 1 :=
      IsogenyQuotient.Field.PolarizationAlternating.Construction.fieldNativePolarizationPairing_alternating (D.pullback s) (pol.pullback s) n hn U z
    rw [ha, hz] at hv
    have hp : e.pairValue p p = 1 := by
      apply (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s U).injective
      exact hv.symm.trans (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s U).map_one.symm
    have he := e.pairValue_natural p (𝟙 H) (𝟙 H)
    simp only [Category.comp_id] at he
    exact he.symm.trans (hp.trans (MonObj.comp_one p).symm)
  exact (congrArg₂ e.pairValue (Category.comp_id x).symm (Category.comp_id x).symm).trans
    ((e.pairValue_natural x (𝟙 H) (𝟙 H)).trans
      ((congrArg (fun z => x ≫ z) hd).trans (MonObj.comp_one x)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingAlternation.Construction
