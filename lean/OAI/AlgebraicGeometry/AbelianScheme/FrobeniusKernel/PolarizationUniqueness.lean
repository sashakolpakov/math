import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization
import OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDualCount

/-! # Polarization Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationUniqueness.Construction

noncomputable section

/-!
On an ordinary geometric fiber, the canonical dual Frobenius is finite.
Thus its pullback identity uniquely determines the full polarization;
finiteness and compatibility with the native group law are proved here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable (q : ℕ) [Fact q.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k q]
variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
variable (hordinary : Nat.card (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)

include pol hordinary in
theorem ordinaryFrobenius_dualMap_finite :
    IsFinite (PicardPullback.Construction.IntrinsicPicardPullback.dualMap
      (Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A).hom
      D (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))))).left := by
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)
  let F := Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime) hS A
  let D' := D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _ hS)
  let f := PicardPullback.Construction.IntrinsicPicardPullback.dualMap F.hom D D'
  have : IsMonHom f := PicardGroupMap.Construction.IntrinsicPicardPullback.dualMap_isMonHom F.hom D D'
  have he : f = Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D q (Fact.out : q.Prime) hS :=
    Polarization.Construction.NativePicardPullback.dualMap_eq_e57 F.hom D D'
  have hc : Nat.card {x : Over.mk (𝟙 (Spec (.of k))) ⟶ D'.abelian.scheme // x ≫ f = 1} = q ^ g := by
    rw [he]
    exact Picard.Homomorphisms.OrdinaryDualCount.Construction.ordinary_dualFrobenius_kernelPointCount q A D pol.isogeny hordinary
  have : Finite (Picard.Homomorphisms.Quotient.Construction.kernelPoints f (Over.mk (𝟙 (Spec (.of k)))) ) :=
    Nat.finite_of_card_ne_zero (hc.trans_ne (pow_ne_zero g (Fact.out : q.Prime).ne_zero))
  have : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :=
    Finite.of_equiv _ (Picard.Homomorphisms.FiniteGroupMaps.Construction.kernelPointEquiv f _).symm
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)
  exact Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel f

include hordinary in
/-- No polarization compatibility or dual-map finiteness is assumed. -/
theorem ordinaryFrobenius_polarization_unique
    (pol' : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))) δ)
    (hp : PolarizationComparison.Construction.polarizationPullbackHom
      (Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A).hom
      D (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))) pol' = pol.isogeny.hom ^ q) :
    pol' = pol.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))) := by
  let F := Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A
  let D' := D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))
  have : IsFinite (PicardPullback.Construction.IntrinsicPicardPullback.dualMap F.hom D D').left :=
    ordinaryFrobenius_dualMap_finite q k D pol hordinary
  exact PolarizationComparison.Construction.polarization_eq_of_pullback_eq F D D' pol' _
    (hp.trans (Polarization.Construction.geometricFrobenius_polarization_pullback q k D pol).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationUniqueness.Construction
