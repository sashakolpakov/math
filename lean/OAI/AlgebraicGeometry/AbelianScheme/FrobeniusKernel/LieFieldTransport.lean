import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualNumberFieldEquiv
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TestBaseChangePoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport

/-! # Lie Field Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.LieFieldTransport.Construction

noncomputable section

/-!
Lie ranks are preserved by actual field isomorphisms. The comparison
uses the original dual-number points, origin, action and scalar maps;
the coordinate bijection in the rank conclusion is transported.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport

variable {k l O : Type} [Field k] [Field l] [CommRing O] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (e : k ≃+* l)

def dualNumberPointsFieldEquiv :
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme) ≃*
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest l ⟶ (A.pullback (Spec.map e.toCommRingCatIso.hom)).scheme) :=
  TestBaseChangePoints.Construction.testBaseChangePointsEquiv A (Spec.map e.toCommRingCatIso.hom) (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso e)

theorem dualNumberPointsFieldEquiv_origin (x : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme) :
    TestBaseChangePoints.Construction.testBaseChangePointsEquiv A (Spec.map e.toCommRingCatIso.hom) (DualNumberFieldEquiv.Construction.fieldPointBaseIso e)
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ x) =
    AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin l ≫ dualNumberPointsFieldEquiv A e x :=
  TestBaseChangePoints.Construction.testBaseChangePointsEquiv_naturality A (Spec.map e.toCommRingCatIso.hom)
    (DualNumberFieldEquiv.Construction.fieldPointBaseIso e) (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso e) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin l)
      (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso_origin e) x

theorem dualNumberPointsFieldEquiv_scalar (a : k) (x : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme) :
    dualNumberPointsFieldEquiv A e (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k a ≫ x) =
      AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar l (e a) ≫ dualNumberPointsFieldEquiv A e x :=
  TestBaseChangePoints.Construction.testBaseChangePointsEquiv_naturality A (Spec.map e.toCommRingCatIso.hom)
    (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso e) (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso e) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k a)
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar l (e a)) (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso_scalar e a) x

variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (τ : O →+* k)

theorem dualNumberPointsFieldEquiv_action (a : O) (x : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme) :
    dualNumberPointsFieldEquiv A e (x ≫ ρ.map a) =
      dualNumberPointsFieldEquiv A e x ≫ (ρ.pullback (Spec.map e.toCommRingCatIso.hom)).map a :=
  TestBaseChangePoints.Construction.testBaseChangePointsEquiv_postcomp A (Spec.map e.toCommRingCatIso.hom)
    (DualNumberFieldEquiv.Construction.dualNumberTestFieldIso e) A (ρ.map a) x

theorem lieFieldTransport_membership (x : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A.scheme) :
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ x = 1 ∧ ∀ a : O, x ≫ ρ.map a = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (τ a) ≫ x) ↔
    (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin l ≫ dualNumberPointsFieldEquiv A e x = 1 ∧ ∀ a : O,
      dualNumberPointsFieldEquiv A e x ≫ (ρ.pullback (Spec.map e.toCommRingCatIso.hom)).map a =
        AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar l (e (τ a)) ≫ dualNumberPointsFieldEquiv A e x) := by
  let φ := dualNumberPointsFieldEquiv A e
  let φ₀ := TestBaseChangePoints.Construction.testBaseChangePointsEquiv A (Spec.map e.toCommRingCatIso.hom) (DualNumberFieldEquiv.Construction.fieldPointBaseIso e)
  constructor
  · rintro ⟨hx, ha⟩
    constructor
    · exact (dualNumberPointsFieldEquiv_origin A e x).symm.trans
        ((congrArg φ₀ hx).trans φ₀.map_one)
    · intro a
      exact (dualNumberPointsFieldEquiv_action A e ρ a x).symm.trans
        ((congrArg φ (ha a)).trans (dualNumberPointsFieldEquiv_scalar A e (τ a) x))
  · rintro ⟨hx, ha⟩
    constructor
    · apply φ₀.injective
      exact (dualNumberPointsFieldEquiv_origin A e x).trans (hx.trans φ₀.map_one.symm)
    · intro a
      apply φ.injective
      exact (dualNumberPointsFieldEquiv_action A e ρ a x).trans
        ((ha a).trans (dualNumberPointsFieldEquiv_scalar A e (τ a) x).symm)

def lieEigenpointsFieldEquiv : AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ ≃
    AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints (A.pullback (Spec.map e.toCommRingCatIso.hom))
      (ρ.pullback (Spec.map e.toCommRingCatIso.hom)) (e.toRingHom.comp τ) :=
  (dualNumberPointsFieldEquiv A e).toEquiv.subtypeEquiv (lieFieldTransport_membership A e ρ τ)

/-- The original additive and scalar-preserving coordinate bijection
gives the same Lie rank after the actual field change. -/
theorem hasLieRank_fieldIso (r : ℕ) (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback (Spec.map e.toCommRingCatIso.hom))
      (ρ.pullback (Spec.map e.toCommRingCatIso.hom)) (e.toRingHom.comp τ) r := by
  obtain ⟨c, hadd, hsmul⟩ := hr
  let v : (Fin r → l) ≃ (Fin r → k) := Equiv.piCongrRight (fun _ => e.symm.toEquiv)
  let φ := dualNumberPointsFieldEquiv A e
  refine ⟨(v.trans c).trans (lieEigenpointsFieldEquiv A e ρ τ), ?_, ?_⟩
  · intro x y
    have hv : v (x + y) = v x + v y := by
      funext i
      exact e.symm.map_add (x i) (y i)
    change φ (c (v (x + y))).val = φ (c (v x)).val * φ (c (v y)).val
    exact (congrArg (fun z => φ (c z).val) hv).trans
      ((congrArg φ (hadd (v x) (v y))).trans (φ.map_mul _ _))
  · intro a x
    have hv : v (a • x) = e.symm a • v x := by
      funext i
      exact e.symm.map_mul a (x i)
    change φ (c (v (a • x))).val = AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar l a ≫ φ (c (v x)).val
    exact (congrArg (fun z => φ (c z).val) hv).trans
      ((congrArg φ (hsmul (e.symm a) (v x))).trans
        ((dualNumberPointsFieldEquiv_scalar A e (e.symm a) (c (v x)).val).trans
          (congrArg (fun b => AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar l b ≫ φ (c (v x)).val) (e.apply_symm_apply a))))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.LieFieldTransport.Construction
