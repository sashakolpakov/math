import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedChosenBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingTestNaturality
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChangeTestLifting

/-! # Prescribed Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedBaseChange.Construction

noncomputable section

/-! Base change transports the independent full-kernel prescription,
including the canonical annihilator condition on every further test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (s : Spec (.of k') ⟶ Spec (.of k)) (n r : ℕ) (labels : (Fin r × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable (H' : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k'
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit (A.pullback s) (ρ.pullback s) (labels (v, false)) n))
variable (eH : ∀ v, (Over.pullback s).obj (H v).group.X ≅ (H' v).group.X)
variable (heH : ∀ v, (eH v).hom ≫ (H' v).inclusion.hom.hom =
  (Over.pullback s).map (H v).inclusion.hom.hom ≫
    (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A.abelian ρ s n (labels (v, false))).hom.hom.hom)

include heH

theorem prescribedFullKernel_baseChange_forward (Q : Over (Spec (.of k')))
    (a : Q ⟶ (A.pullback s).abelian.scheme)
    (ha : Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H ((Over.map s).obj Q)
      (A.abelian.baseChangePointsMulEquiv s Q a)) :
    Prescription.Construction.prescribedFullKernel j iota hsplit (A.pullback s) (ρ.pullback s) n r labels H' Q a := by
  obtain ⟨x0, hx0, hcond⟩ := ha
  let e := A.abelian.torsionBaseChangeEquiv s Q (q ^ n)
  let x := e.symm x0
  have hx : x.val = a := by
    apply (A.abelian.baseChangePointsMulEquiv s Q).injective
    exact (congrArg Subtype.val (e.apply_symm_apply x0)).trans hx0
  refine ⟨x, hx, fun v => ⟨?_, ?_⟩⟩
  · obtain ⟨h, hh⟩ := (hcond v).1
    let hp := (Over.mapPullbackAdj s).homEquiv Q (H v).group.X h
    refine ⟨hp ≫ (eH v).hom, ?_⟩
    apply e.injective
    have hc := PrescribedChosenBaseChange.Construction.prescribedChosenPoint_baseChange j iota hsplit A ρ s n (labels (v, false))
      (H v) (H' v) (eH v).hom (heH v) Q hp
    have hhp := ((Over.mapPullbackAdj s).homEquiv Q (H v).group.X).symm_apply_apply h
    have hb := PrescribedBlockBaseChange.Construction.prescribedBlockComponent_baseChange j iota hsplit A ρ s n (labels (v, false)) Q x
    exact hc.trans ((congrArg
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) ((Over.map s).obj Q)) hhp).trans
      (hh.trans ((congrArg
        (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) ((Over.map s).obj Q))
        (e.apply_symm_apply x0)).symm.trans hb.symm)))
  · intro U t h
    let h0 := ((Over.mapPullbackAdj s).homEquiv U (H v).group.X).symm (h ≫ (eH v).inv)
    have ho := (hcond v).2 ((Over.map s).obj U) ((Over.map s).map t) h0
    apply (CanonicalPairingBaseChange.Construction.canonicalTorsionOrthogonal_baseChange A s (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U _ _).mpr
    have hc := PrescribedChosenBaseChange.Construction.prescribedChosenPoint_baseChange_iso j iota hsplit A ρ s n (labels (v, false))
      (H v) (H' v) (eH v) (heH v) U h
    have hb := PrescribedBlockBaseChange.Construction.prescribedBlockComponent_baseChange j iota hsplit A ρ s n (labels (v, true)) U
      (((A.pullback s).abelian.torsionFunctor (q ^ n)).map t.op x)
    have ht := (A.abelian.torsionBaseChangeIso s (q ^ n)).hom.naturality_apply t.op x
    have hx0 : e x = x0 := e.apply_symm_apply x0
    have hp := ht.trans (congrArg
      ((A.abelian.torsionFunctor (q ^ n)).map ((Over.map s).map t).op) hx0)
    have hb' := hb.trans (congrArg
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) ((Over.map s).obj U)) hp)
    exact (congrArg₂ (Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) ((Over.map s).obj U)) hc hb').mpr ho

theorem prescribedFullKernel_baseChange_backward (Q : Over (Spec (.of k')))
    (a : Q ⟶ (A.pullback s).abelian.scheme)
    (ha : Prescription.Construction.prescribedFullKernel j iota hsplit (A.pullback s) (ρ.pullback s) n r labels H' Q a) :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H ((Over.map s).obj Q)
      (A.abelian.baseChangePointsMulEquiv s Q a) := by
  obtain ⟨x, hx, hcond⟩ := ha
  let x0 := A.abelian.torsionBaseChangeEquiv s Q (q ^ n) x
  refine ⟨x0, congrArg (A.abelian.baseChangePointsMulEquiv s Q) hx, fun v => ⟨?_, ?_⟩⟩
  · obtain ⟨h, hh⟩ := (hcond v).1
    let h0 := ((Over.mapPullbackAdj s).homEquiv Q (H v).group.X).symm (h ≫ (eH v).inv)
    refine ⟨h0, ?_⟩
    have hc := PrescribedChosenBaseChange.Construction.prescribedChosenPoint_baseChange_iso j iota hsplit A ρ s n (labels (v, false))
      (H v) (H' v) (eH v) (heH v) Q h
    have hb := PrescribedBlockBaseChange.Construction.prescribedBlockComponent_baseChange j iota hsplit A ρ s n (labels (v, false)) Q x
    exact hc.symm.trans ((congrArg (A.abelian.torsionBaseChangeEquiv s Q (q ^ n)) hh).trans hb)
  · intro U t h
    let V := BaseChangeTestLifting.Construction.liftedBaseChangeTest s t
    let eU := BaseChangeTestLifting.Construction.liftedBaseChangeTestIso s t
    let t' := BaseChangeTestLifting.Construction.liftedBaseChangeTestMap s t
    let dp := (Over.mapPullbackAdj s).homEquiv V (H v).group.X (eU.hom ≫ h)
    have ho' := (hcond v).2 V t' (dp ≫ (eH v).hom)
    have ho := (CanonicalPairingBaseChange.Construction.canonicalTorsionOrthogonal_baseChange A s (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) V _ _).mp ho'
    have hc := PrescribedChosenBaseChange.Construction.prescribedChosenPoint_baseChange j iota hsplit A ρ s n (labels (v, false))
      (H v) (H' v) (eH v).hom (heH v) V dp
    have hdp := ((Over.mapPullbackAdj s).homEquiv V (H v).group.X).symm_apply_apply (eU.hom ≫ h)
    have hnat := (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_natural j iota hsplit A ρ n (labels (v, false))
      eU.hom (h ≫ (H v).inclusion.hom.hom)).trans
        (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, false))
          ((Over.map s).obj V)) (Category.assoc eU.hom h (H v).inclusion.hom.hom).symm)
    have hleft := hc.trans ((congrArg
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) ((Over.map s).obj V)) hdp).trans
        hnat.symm)
    have hp0 : A.abelian.torsionBaseChangeEquiv s V (q ^ n)
        (((A.pullback s).abelian.torsionFunctor (q ^ n)).map t'.op x) =
      (A.abelian.torsionFunctor (q ^ n)).map eU.hom.op
        ((A.abelian.torsionFunctor (q ^ n)).map t.op x0) := by
      apply Subtype.ext
      exact (TestBaseChangePoints.Construction.baseChangePoints_precomp A.abelian s t' x.val).trans
        ((congrArg (fun z => z ≫ x0.val) (BaseChangeTestLifting.Construction.liftedBaseChangeTestMap_square s t)).trans
          (Category.assoc eU.hom t x0.val))
    have hb := PrescribedBlockBaseChange.Construction.prescribedBlockComponent_baseChange j iota hsplit A ρ s n (labels (v, true)) V
      (((A.pullback s).abelian.torsionFunctor (q ^ n)).map t'.op x)
    have hright := hb.trans ((congrArg
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) ((Over.map s).obj V)) hp0).trans
        (CanonicalBlockComponents.Construction.prescribedBlockComponent_natural j iota hsplit A ρ n (labels (v, true)) eU.hom
          ((A.abelian.torsionFunctor (q ^ n)).map t.op x0)).symm)
    have htest := (congrArg₂ (Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) ((Over.map s).obj V)) hleft hright).mp ho
    exact (CanonicalPairingTestNaturality.Construction.canonicalTorsionOrthogonal_testIso A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) eU _ _).mp htest

theorem prescribedFullKernel_baseChange (Q : Over (Spec (.of k')))
    (a : Q ⟶ (A.pullback s).abelian.scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit (A.pullback s) (ρ.pullback s) n r labels H' Q a ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H ((Over.map s).obj Q)
        (A.abelian.baseChangePointsMulEquiv s Q a) :=
  ⟨prescribedFullKernel_baseChange_backward j iota hsplit A ρ s n r labels H H' eH heH Q a,
    prescribedFullKernel_baseChange_forward j iota hsplit A ρ s n r labels H H' eH heH Q a⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedBaseChange.Construction
