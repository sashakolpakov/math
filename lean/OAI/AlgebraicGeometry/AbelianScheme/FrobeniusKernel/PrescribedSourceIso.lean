import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourcePoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPairingIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Prescribed Source Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourceIso.Construction

noncomputable section

/-! A full polarized source isomorphism transports the independent
kernel prescription through the actual chosen subgroup inclusion squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
variable (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)
variable (he : ∀ z : NumberField.RingOfIntegers E, ρ.map z ≫ e.abelian.hom = e.abelian.hom ≫ σ.map z)
variable (n r : ℕ) (labels : (Fin r × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable (J : ∀ v : Fin r, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit B σ (labels (v, false)) n))
variable (eH : ∀ v, (H v).group.X ≅ (J v).group.X)
variable (heH : ∀ v, (eH v).hom ≫ (J v).inclusion.hom.hom = (H v).inclusion.hom.hom ≫
  (PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit A.abelian B.abelian ρ σ e.abelian.hom he n (labels (v, false))).hom.hom)

include heH

theorem prescribedFullKernel_sourceIso_forward (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (ha : Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H T a) :
    Prescription.Construction.prescribedFullKernel j iota hsplit B σ n r labels J T (a ≫ e.abelian.hom) := by
  obtain ⟨x, hx, hcond⟩ := ha
  let f := PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian e.abelian.hom (q ^ n)
  refine ⟨f.app (.op T) x, congrArg (fun z => z ≫ e.abelian.hom) hx, fun v => ⟨?_, ?_⟩⟩
  · obtain ⟨h, hh⟩ := (hcond v).1
    refine ⟨h ≫ (eH v).hom, ?_⟩
    have hc := PrescribedSourcePoints.Construction.prescribedChosenPoint_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, false)) (H v) (J v) (eH v).hom (heH v) T h
    exact hc.symm.trans ((congrArg (f.app (.op T)) hh).trans
      (PrescribedSourcePoints.Construction.prescribedBlockComponent_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
        (labels (v, false)) T x))
  · intro U t h
    let h0 := h ≫ (eH v).inv
    have ho := (hcond v).2 U t h0
    have hpair := (CanonicalPairingIsomorphism.Construction.canonicalTorsionOrthogonal_levelIso A B e (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U _ _).mpr ho
    have hc := PrescribedSourcePoints.Construction.prescribedChosenPoint_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, false)) (H v) (J v) (eH v).hom (heH v) U h0
    have hh : h0 ≫ (eH v).hom = h := by
      exact (Category.assoc h (eH v).inv (eH v).hom).trans
        ((congrArg (fun z => h ≫ z) (eH v).inv_hom_id).trans (Category.comp_id h))
    have hc' := hc.trans (congrArg
      (Prescription.Construction.prescribedChosenPoint j iota hsplit B σ n (labels (v, false)) (J v) U) hh)
    have hb := (PrescribedSourcePoints.Construction.prescribedBlockComponent_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, true)) U ((A.abelian.torsionFunctor (q ^ n)).map t.op x)).trans
        (congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit B σ n (labels (v, true)) U)
          (f.naturality_apply t.op x))
    exact (congrArg₂ (Prescription.Construction.canonicalTorsionOrthogonal B (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U) hc' hb).mp hpair

theorem prescribedFullKernel_sourceIso_backward (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (ha : Prescription.Construction.prescribedFullKernel j iota hsplit B σ n r labels J T (a ≫ e.abelian.hom)) :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H T a := by
  obtain ⟨y, hy, hcond⟩ := ha
  let f := PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian B.abelian e.abelian.hom (q ^ n)
  let et := AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionPointsIso e.abelian (q ^ n) T
  let x := et.symm y
  have hxy : f.app (.op T) x = y := et.apply_symm_apply y
  have hx : x.val = a := by
    apply (cancel_mono e.abelian.hom).mp
    exact (congrArg Subtype.val hxy).trans hy
  refine ⟨x, hx, fun v => ⟨?_, ?_⟩⟩
  · obtain ⟨h, hh⟩ := (hcond v).1
    refine ⟨h ≫ (eH v).inv, ?_⟩
    apply et.injective
    have hc := PrescribedSourcePoints.Construction.prescribedChosenPoint_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, false)) (H v) (J v) (eH v).hom (heH v) T (h ≫ (eH v).inv)
    have hh0 : (h ≫ (eH v).inv) ≫ (eH v).hom = h := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hc' := hc.trans (congrArg
      (Prescription.Construction.prescribedChosenPoint j iota hsplit B σ n (labels (v, false)) (J v) T) hh0)
    have hb := PrescribedSourcePoints.Construction.prescribedBlockComponent_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, false)) T x
    exact hc'.trans (hh.trans ((congrArg
      (Prescription.Construction.prescribedBlockComponent j iota hsplit B σ n (labels (v, false)) T) hxy).symm.trans hb.symm))
  · intro U t h
    have ho := (hcond v).2 U t (h ≫ (eH v).hom)
    have hc := PrescribedSourcePoints.Construction.prescribedChosenPoint_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, false)) (H v) (J v) (eH v).hom (heH v) U h
    have hp := (f.naturality_apply t.op x).trans
      (congrArg ((B.abelian.torsionFunctor (q ^ n)).map t.op) hxy)
    have hb := (PrescribedSourcePoints.Construction.prescribedBlockComponent_sourceMap j iota hsplit A B ρ σ e.abelian.hom he n
      (labels (v, true)) U ((A.abelian.torsionFunctor (q ^ n)).map t.op x)).trans
        (congrArg (Prescription.Construction.prescribedBlockComponent j iota hsplit B σ n (labels (v, true)) U) hp)
    have hpair := (congrArg₂ (Prescription.Construction.canonicalTorsionOrthogonal B (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U) hc hb).mpr ho
    exact (CanonicalPairingIsomorphism.Construction.canonicalTorsionOrthogonal_levelIso A B e (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U _ _).mp hpair

theorem prescribedFullKernel_sourceIso (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit B σ n r labels J T (a ≫ e.abelian.hom) ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n r labels H T a :=
  ⟨prescribedFullKernel_sourceIso_backward j iota hsplit A B ρ σ e he n r labels H J eH heH T a,
    prescribedFullKernel_sourceIso_forward j iota hsplit A B ρ σ e he n r labels H J eH heH T a⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSourceIso.Construction
