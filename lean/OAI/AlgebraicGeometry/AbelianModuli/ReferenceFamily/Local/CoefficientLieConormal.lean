import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieSpace

/-! # Coefficient Lie Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieConormal.LocalCoefficientLie

noncomputable section

section

/-! Actual coordinate-ring lifts of local-coefficient infinitesimal
section points. Both coefficients and all linear operations are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {X Y : Scheme.{0}} [IsAffine X] (p : Y ⟶ X) (s : X ⟶ Y)
  (hs : s ≫ p = 𝟙 X) {C : Type} [CommRing C] [IsLocalRing C] (q : Spec (.of C) ⟶ X)

def algebraLift (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    letI := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
    letI := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
    Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C Γ(X, ⊤) Γ(Y, ⊤) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  let := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
  let := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
  let e := Scheme.stalkClosedPointTo (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q)
  refine ⟨⟨(PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.toGlobal (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) e v.val).hom, ?_⟩, ?_⟩
  · intro b
    have h := v.val.congruent (Y.presheaf.Γgerm ((CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) (IsLocalRing.closedPoint (DualNumber C))) b)
    change _ - PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.globalMap e b ∈ Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C at h
    rw [CoefficientLieSpace.LocalCoefficientLie.reference_eq s q] at h
    exact h
  · intro r
    have h := (PELModuli.IntegralModel.Affine.RelativeLifts.AffineStalkLifts.toGlobal_relative_iff p (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) e v.val).mp v.property r
    exact h.trans ((RingHom.congr_fun (CoefficientLieSpace.LocalCoefficientLie.reference_eq s q) (p.appTop r)).trans
      (IsScalarTower.algebraMap_apply Γ(X, ⊤) Γ(Y, ⊤) (DualNumber C) r).symm)

theorem algebraLift_hom (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) (b : Γ(Y, ⊤)) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    letI := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
    letI := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
    (algebraLift p s hs q v).val.hom b =
      v.val.hom (Y.presheaf.Γgerm ((CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) (IsLocalRing.closedPoint (DualNumber C))) b) := rfl

def toAlgebraLifts :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    letI := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
    letI := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
    CoefficientLieSpace.LocalCoefficientLie.Space p s q →ₗ[DualNumber C] Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C Γ(X, ⊤) Γ(Y, ⊤) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  let := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
  let := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
  refine { toFun := algebraLift p s hs q, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    change (v.val + w.val).hom (Y.presheaf.Γgerm _ b) =
      (algebraLift p s hs q v).val.hom b + (algebraLift p s hs q w).val.hom b -
        algebraMap Γ(Y, ⊤) (DualNumber C) b
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.add_hom, algebraLift_hom, algebraLift_hom]
    exact congrArg (fun z => v.val.hom (Y.presheaf.Γgerm _ b) +
      w.val.hom (Y.presheaf.Γgerm _ b) - z) (RingHom.congr_fun (CoefficientLieSpace.LocalCoefficientLie.reference_eq s q) b)
  · intro c v
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    change (c • v.val).hom (Y.presheaf.Γgerm _ b) =
      algebraMap Γ(Y, ⊤) (DualNumber C) b +
        c * ((algebraLift p s hs q v).val.hom b - algebraMap Γ(Y, ⊤) (DualNumber C) b)
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.smul_hom, algebraLift_hom]
    exact congrArg (fun z => z + c * (v.val.hom (Y.presheaf.Γgerm _ b) - z))
      (RingHom.congr_fun (CoefficientLieSpace.LocalCoefficientLie.reference_eq s q) b)

end

/-! The actual infinitesimal section points over any local coefficient
ring identify with the coefficient dual of the original smooth conormal
module. The comparison includes its formula on every conormal generator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
  (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
  {C : Type} [CommRing C] [IsLocalRing C] (q : Spec (.of C) ⟶ X)

theorem toAlgebraLifts_bijective :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    letI := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
    letI := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
    Function.Bijective (toAlgebraLifts p s hs q) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  let := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
  let := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
  let e := Scheme.stalkClosedPointTo (CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q)
  constructor
  · intro v w h
    apply Subtype.ext
    apply (PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.toGlobal_bijective (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) e).injective
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    exact congrArg (fun z : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C Γ(X, ⊤) Γ(Y, ⊤) => z.val.hom b) h
  · intro w
    let w₀ : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C)
        (PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.globalMap e) := ⟨w.val.hom, fun b => by
          rw [CoefficientLieSpace.LocalCoefficientLie.reference_eq s q]
          exact w.val.congruent b⟩
    obtain ⟨v, hg⟩ := (PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.toGlobal_bijective (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) e).surjective w₀
    have hv : v ∈ AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
        (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) e p := by
      apply (PELModuli.IntegralModel.Affine.RelativeLifts.AffineStalkLifts.toGlobal_relative_iff p (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
        (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) e v).mpr
      intro r
      have hr := congrArg (fun z : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
        (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) (PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.globalMap e) => z.hom (p.appTop r)) hg
      exact hr.trans ((w.property r).trans
        ((IsScalarTower.algebraMap_apply Γ(X, ⊤) Γ(Y, ⊤) (DualNumber C) r).trans
          (RingHom.congr_fun (CoefficientLieSpace.LocalCoefficientLie.reference_eq s q) (p.appTop r)).symm))
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    exact congrArg (fun z : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) (PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.globalMap e) => z.hom b) hg

def algebraEquiv :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    letI := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
    letI := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
    CoefficientLieSpace.LocalCoefficientLie.Space p s q ≃ₗ[C] Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C Γ(X, ⊤) Γ(Y, ⊤) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  let := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
  let := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
  exact (LinearEquiv.ofBijective (toAlgebraLifts p s hs q)
    (toAlgebraLifts_bijective p s hs q)).restrictScalars C

theorem algebraEquiv_hom (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) (b : Γ(Y, ⊤)) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    letI := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
    letI := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
    (algebraEquiv p s hs q v).val.hom b =
      v.val.hom (Y.presheaf.Γgerm ((CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) (IsLocalRing.closedPoint (DualNumber C))) b) := rfl

def conormalEquiv [Smooth p] :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    CoefficientLieSpace.LocalCoefficientLie.Space p s q ≃ₗ[C] ((RingHom.ker s.appTop.hom).Cotangent →ₗ[Γ(X, ⊤)] C) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  let := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
  let := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  exact (algebraEquiv p s hs q).trans (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C Γ(X, ⊤) Γ(Y, ⊤))

theorem conormalEquiv_toCotangent [Smooth p] (v : CoefficientLieSpace.LocalCoefficientLie.Space p s q) (b : RingHom.ker s.appTop.hom) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    conormalEquiv p s hs q v (Ideal.toCotangent _ b) =
      (v.val.hom (Y.presheaf.Γgerm ((CoefficientLieSpace.LocalCoefficientLie.zeroPoint s q) (IsLocalRing.closedPoint (DualNumber C))) b)).snd := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  let := CoefficientLieSpace.LocalCoefficientLie.ambientCoefficientAlgebra s q
  let := CoefficientLieSpace.LocalCoefficientLie.coefficientScalarTower p s q hs
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  change Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv C Γ(X, ⊤) Γ(Y, ⊤) (algebraEquiv p s hs q v)
    (Ideal.toCotangent _ b) = _
  rw [Dual.AlgebraLiftCoordinates.DualCoefficientLifts.conormalEquiv_toCotangent, algebraEquiv_hom]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieConormal.LocalCoefficientLie
