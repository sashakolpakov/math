import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProperReciprocity
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.RegularFactorization

/-! # Branch Factorization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.BranchFactorization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: cleared ring factorizations in the actual affine stalk and function field

Numerators and denominators outside P supply actual units in the
geometric stalk. The canonical stalk isomorphism carries the chosen
localization uniformizer to an irreducible germ.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R]

local instance affineBranchFactorization_stalkAlgebra (x : Spec (CommRingCat.of R)) :
    Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x

def affineBranchStalkUnit (P : Ideal R) [P.IsPrime] (a : R) (ha : a ∉ P) :
    ((Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P))ˣ :=
  (ProperReciprocity.BundleCycles.affineRegularGerm_isUnit R a (PrimeSupport.BundleCycles.affinePrimePoint R P) ha).unit

omit [IsDomain R] in
theorem affineBranchStalkUnit_val (P : Ideal R) [P.IsPrime] (a : R) (ha : a ∉ P) :
    (affineBranchStalkUnit R P a ha : (Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) =
      (Spec (CommRingCat.of R)).presheaf.germ ⊤ (PrimeSupport.BundleCycles.affinePrimePoint R P) (by trivial) (Divisor.BundleCycles.affineAmbientSection R a) :=
  (ProperReciprocity.BundleCycles.affineRegularGerm_isUnit R a (PrimeSupport.BundleCycles.affinePrimePoint R P) ha).unit_spec

omit [IsDomain R] in
theorem affineBranch_uniformizer_irreducible (P : Ideal R) [P.IsPrime] (t : R)
    (ht : Irreducible (algebraMap R (Localization P.primeCompl) t)) :
    Irreducible ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (PrimeSupport.BundleCycles.affinePrimePoint R P) (by trivial)
      (Divisor.BundleCycles.affineAmbientSection R t)) := by
  let e : Localization.AtPrime P ≃ₐ[R] (Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P) :=
    StructureSheaf.stalkIso R (show PrimeSpectrum R from PrimeSupport.BundleCycles.affinePrimePoint R P)
  have he := ht.map e.toMulEquiv
  change Irreducible (e (algebraMap R (Localization.AtPrime P) t)) at he
  rw [e.commutes] at he
  exact he

theorem affineBranchStalkUnit_fraction (P : Ideal R) [P.IsPrime] (a : R) (ha : a ∉ P) :
    algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P))
      (Spec (CommRingCat.of R)).functionField (affineBranchStalkUnit R P a ha : _) =
        RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R a) := by
  rw [affineBranchStalkUnit_val]
  exact Scheme.algebraMap_germ_eq_germToFunctionField _ (by trivial) _

theorem affineFunctionUnit_branch_factor (P : Ideal R) [P.IsPrime]
    (a t u s : R) (ha : a ≠ 0) (hu : u ∉ P) (hs : s ∉ P) (m : ℕ)
    (hsa : s * a = u * t ^ m) :
    (ProperReciprocity.BundleCycles.affineFunctionUnit R a ha : (Spec (CommRingCat.of R)).functionField) =
      (affineBranchStalkUnit R P u hu / affineBranchStalkUnit R P s hs) •
        (algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P))
          (Spec (CommRingCat.of R)).functionField
          ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (PrimeSupport.BundleCycles.affinePrimePoint R P) (by trivial)
            (Divisor.BundleCycles.affineAmbientSection R t))) ^ (m : ℤ) := by
  let X := Spec (CommRingCat.of R)
  let F : R →+* X.functionField := (X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have he : F s * F a = F u * (F t) ^ m := by
    rw [← map_mul, hsa, map_mul, map_pow]
  have hs0 : F s ≠ 0 := by
    have hsu := affineBranchStalkUnit_fraction R P s hs
    exact hsu ▸ (affineBranchStalkUnit R P s hs).isUnit.map (algebraMap _ X.functionField) |>.ne_zero
  change F a = _
  rw [Units.smul_def, Algebra.smul_def, zpow_natCast]
  change F a = (Units.map (algebraMap _ X.functionField).toMonoidHom
    (affineBranchStalkUnit R P u hu / affineBranchStalkUnit R P s hs) : X.functionField) * _
  rw [map_div, Units.val_div_eq_div_val]
  change F a = (algebraMap (X.presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) X.functionField
    (affineBranchStalkUnit R P u hu : X.presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) /
    algebraMap (X.presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) X.functionField
    (affineBranchStalkUnit R P s hs : X.presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P))) * _
  rw [affineBranchStalkUnit_fraction, affineBranchStalkUnit_fraction]
  have htF : algebraMap (X.presheaf.stalk (PrimeSupport.BundleCycles.affinePrimePoint R P)) X.functionField
      (X.presheaf.germ ⊤ (PrimeSupport.BundleCycles.affinePrimePoint R P) (by trivial) (Divisor.BundleCycles.affineAmbientSection R t)) = F t :=
    Scheme.algebraMap_germ_eq_germToFunctionField X (by trivial) (Divisor.BundleCycles.affineAmbientSection R t)
  rw [htF]
  change F a = (F u / F s) * (F t) ^ m
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hs0).mpr ((mul_comm (F a) (F s)).trans he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.BranchFactorization.BundleCycles
