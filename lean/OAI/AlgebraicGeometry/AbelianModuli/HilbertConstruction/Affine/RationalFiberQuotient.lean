import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveRingPushoutQuotient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalPointIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Rational Fiber Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalFiberQuotient

noncomputable section

/-! The actual affine fiber at a rational section has coordinate algebra the
quotient by the extended point ideal, with its ground-field scalar action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def affineRationalFiberQuotientCoefficientIso
    {K : Type u} [Field K] {T Y Z : Scheme.{u}} [IsAffine T] [IsAffine Y]
    (p : T ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ T) (hz : z ≫ p = 𝟙 _)
    {s : Y ⟶ T} {a : Z ⟶ Y} {b : Z ⟶ Spec (.of K)} (H : IsPullback a b s z) :
    let : Algebra K Γ(Z, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap b).toAlgebra;
    (ModuleCat.restrictScalars (Coefficient.ModulePresheaf.schemeCoefficientMap (s ≫ p))).obj
      (ModuleCat.of Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ (RationalPointIdeal.affineRationalPointIdeal z).map s.appTop.hom)) ≅
        ModuleCat.of K Γ(Z, ⊤) := by
  let : Algebra K Γ(Y, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap (s ≫ p)).toAlgebra
  let : Algebra K Γ(Z, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap b).toAlgebra
  have hI : RationalPointIdeal.affineRationalPointIdeal z = RingHom.ker z.appTop.hom := by
    rw [RationalPointIdeal.affineRationalPointIdeal_eq_kernel]
    exact RingHom.ker_comp_of_injective z.appTop.hom
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id p z hz
  have hsurj : Function.Surjective z.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine z).2
  have hpush : IsPushout s.appTop z.appTop a.appTop b.appTop := isPushout_appTop_of_isPullback H
  have hbase : a ≫ (s ≫ p) = b := by
    rw [← Category.assoc, H.w, Category.assoc, hz, Category.comp_id]
  have hcoef (k : K) : a.appTop.hom (algebraMap K Γ(Y, ⊤) k) = algebraMap K Γ(Z, ⊤) k := by
    change (a ≫ (s ≫ p)).appTop ((Scheme.ΓSpecIso (.of K)).inv k) =
      b.appTop ((Scheme.ΓSpecIso (.of K)).inv k)
    exact congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (.of K)).inv k)) hbase
  let e := SurjectiveRingPushoutQuotient.pushoutQuotientAlgEquivOfSurjective (K := K)
    s.appTop.hom z.appTop.hom a.appTop.hom b.appTop.hom hpush hsurj hcoef
  let eI := Ideal.quotientEquivAlgOfEq K (congrArg (fun I : Ideal Γ(T, ⊤) => I.map s.appTop.hom) hI)
  exact (eI.trans e).toLinearEquiv.toModuleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalFiberQuotient
