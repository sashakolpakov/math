import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # Prescription Actions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions.Construction

noncomputable section

section

/-! The canonical comparison with the original torsion points retains
the subgroup inclusion and every original abelian endomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (n : ℕ)

theorem originalTorsionSheafPoint_inclusion (T : Over (Spec (.of k)))
    (x : (A.torsionFunctor n).obj (.op T)) :
    (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk A.scheme)) n)).hom.app (.op T)
      (Prescription.Construction.originalTorsionSheafPoint A n T x) = ULift.up x.val := by
  let e := ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A n).app (.op T)).groupIsoToMulEquiv
  let z := e.symm x
  have hz : z ≫ TorsionQuotient.SubgroupFunctor.torsionι A.scheme n = x.val :=
    (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso_value A n T z).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply x))
  have h := congrArg (fun f => f.hom.app (.op T) (ULift.up z))
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_inclusion (Grp.mk A.scheme) n)
  exact h.trans (congrArg ULift.up hz)

theorem originalTorsionSheafInclusion_injective (T : Over (Spec (.of k))) :
    Function.Injective ((kernel.ι
      (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (Grp.mk A.scheme)) n)).hom.app (.op T)) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (Prescription.Construction.originalTorsionSheafPoint_bijective A n T).surjective x
  obtain ⟨b, rfl⟩ := (Prescription.Construction.originalTorsionSheafPoint_bijective A n T).surjective y
  have hab : ULift.up a.val = ULift.up b.val :=
    (originalTorsionSheafPoint_inclusion A n T a).symm.trans
      (h.trans (originalTorsionSheafPoint_inclusion A n T b))
  exact congrArg (Prescription.Construction.originalTorsionSheafPoint A n T)
    (Subtype.ext (congrArg ULift.down hab))

theorem originalTorsionSheafPoint_endomorphism
    (p : A.scheme ⟶ A.scheme) [IsMonHom p]
    (T : Over (Spec (.of k))) (x : (A.torsionFunctor n).obj (.op T)) :
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.scheme p)) n).hom.app (.op T)
        (Prescription.Construction.originalTorsionSheafPoint A n T x) =
      Prescription.Construction.originalTorsionSheafPoint A n T ((PELModuli.CMPoints.DualityPairing.homOnTorsion A A p n).app (.op T) x) := by
  apply originalTorsionSheafInclusion_injective A n T
  let f := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.scheme p)
  have h := congrArg (fun t => t.hom.app (.op T) (Prescription.Construction.originalTorsionSheafPoint A n T x))
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion f n)
  exact h.trans
    ((congrArg (fun z => f.hom.app (.op T) z) (originalTorsionSheafPoint_inclusion A n T x)).trans
      (originalTorsionSheafPoint_inclusion A n T
        ((PELModuli.CMPoints.DualityPairing.homOnTorsion A A p n).app (.op T) x)).symm)

theorem originalTorsionSheafMap_eq_of_action
    (p r : A.scheme ⟶ A.scheme) [IsMonHom p] [IsMonHom r]
    (h : PELModuli.CMPoints.DualityPairing.homOnTorsion A A p n = PELModuli.CMPoints.DualityPairing.homOnTorsion A A r n) :
    CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.scheme p)) n =
      CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.scheme r)) n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := (Prescription.Construction.originalTorsionSheafPoint_bijective A n T.unop).surjective x
  have hx := ConcreteCategory.congr_hom (NatTrans.congr_app h T) x
  exact (originalTorsionSheafPoint_endomorphism A n p T.unop x).trans
    ((congrArg (Prescription.Construction.originalTorsionSheafPoint A n T.unop) hx).trans
      (originalTorsionSheafPoint_endomorphism A n r T.unop x).symm)

end

/-! The exact canonical kernel prescription is stable under the original
integral action. Scalar block actions and bilinearity suffice on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem canonicalTorsionOrthogonal_pow_right (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor m).obj (.op T))
    (h : Prescription.Construction.canonicalTorsionOrthogonal A m hm T x y) (r : ℕ) :
    Prescription.Construction.canonicalTorsionOrthogonal A m hm T x (y ^ r) := by
  let e := CartierDualityCanonical.Construction.e56SourceTorsionPairing A m hm
  let px := Prescription.Construction.originalTorsionSheafPoint A.abelian m T x
  let py := Prescription.Construction.originalTorsionSheafPoint A.abelian m T y
  let f := CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue
    (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) m) T
    (e.leftAdjoint.hom.app (.op T) px)
  have hf : f py = 1 := (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.adjoint_value e T px py).symm.trans h
  have hp := (Prescription.Construction.originalTorsionSheafPointMulEquiv A.abelian m T).toMonoidHom.map_pow y r
  exact (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.adjoint_value e T px (Prescription.Construction.originalTorsionSheafPoint A.abelian m T (y ^ r))).trans
    ((congrArg f hp).trans ((f.map_pow py r).trans
      ((congrArg (fun z => z ^ r) hf).trans (one_pow r))))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_pow
    (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) (h : T ⟶ H.group.X) (r : ℕ) :
    Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T (h ^ r) =
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h) ^ r := by
  let f := (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom ≫
    PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n
  exact (congrArg (fun z => f.app (.op T) z) (MonObj.pow_comp h r H.inclusion.hom.hom)).trans
    ((f.app (.op T)).hom.map_pow (h ≫ H.inclusion.hom.hom) r)

omit [IsAlgClosed k] in
theorem prescribedBlockComponent_action_scalar (a : NumberField.RingOfIntegers E)
    (T : Over (Spec (.of k))) (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T
      ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian A.abelian (ρ.map a) (q ^ n)).app (.op T) x) =
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x) ^
        (PadicInt.toZModPow n (j.localCharacter iota τ a)).val := by
  let c := j.projector iota hsplit n τ
  have hc : ρ.map a ≫ ρ.map c = ρ.map c ≫ ρ.map a :=
    (ρ.map_mul c a).symm.trans ((congrArg ρ.map (mul_comm c a)).trans (ρ.map_mul a c))
  have hs := ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A.abelian ρ n τ).app (.op T) x).property.2 a
  apply Subtype.ext
  exact (Category.assoc x.val (ρ.map a) (ρ.map c)).trans
    ((congrArg (fun f => x.val ≫ f) hc).trans
      ((Category.assoc x.val (ρ.map c) (ρ.map a)).symm.trans hs))

omit τ in
theorem prescribedFullKernel_action (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
    (a : NumberField.RingOfIntegers E) (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme)
    (hx : Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T x) :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T (x ≫ ρ.map a) := by
  obtain ⟨z, hz, hcond⟩ := hx
  let f := PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian A.abelian (ρ.map a) (q ^ n)
  refine ⟨f.app (.op T) z, congrArg (fun t => t ≫ ρ.map a) hz, ?_⟩
  intro v
  constructor
  · obtain ⟨h, hh⟩ := (hcond v).1
    let r := (PadicInt.toZModPow n (j.localCharacter iota (labels (v, false)) a)).val
    refine ⟨h ^ r, ?_⟩
    exact (prescribedChosenPoint_pow A j iota hsplit ρ n (labels (v, false)) (H v) T h r).trans
      ((congrArg (fun t => t ^ r) hh).trans
        (prescribedBlockComponent_action_scalar A j iota hsplit ρ n (labels (v, false)) a T z).symm)
  · intro U t h
    let r := (PadicInt.toZModPow n (j.localCharacter iota (labels (v, true)) a)).val
    have ho := canonicalTorsionOrthogonal_pow_right A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U
        ((A.abelian.torsionFunctor (q ^ n)).map t.op z)) ((hcond v).2 U t h) r
    have hc := (congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U)
      (f.naturality_apply t.op z).symm).trans
        (prescribedBlockComponent_action_scalar A j iota hsplit ρ n (labels (v, true)) a U
          ((A.abelian.torsionFunctor (q ^ n)).map t.op z))
    exact (congrArg (fun y => Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h) y) hc).mpr ho

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions.Construction
