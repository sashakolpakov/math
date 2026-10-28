import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices

/-! # Preimage Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PreimageQuotient

noncomputable section

/-! The target integral Tate module is the intrinsic preimage lattice.
Under this equivalence, the source image is the image of the isogeny's
integral Tate map. Their quotients are therefore the same cokernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime] (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def targetToTatePreimage : Add.schemeTateModule B.scheme (Over.mk b) q →ₗ[ℤ_[q]]
    Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom :=
  (((GeometricIsogeny.geometricTateIsogenyEquiv b q f).symm.toLinearMap.restrictScalars ℤ_[q]).comp
    (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.schemeTateModule B.scheme (Over.mk b) q) 1)).codRestrict _ (by
      intro y
      change (GeometricIsogeny.geometricTateIsogenyEquiv b q f)
        ((GeometricIsogeny.geometricTateIsogenyEquiv b q f).symm (1 ⊗ₜ[ℤ_[q]] y)) ∈
          Rational.integralTateImage B.scheme (Over.mk b) q
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨y, rfl⟩)

theorem targetToTatePreimage_bijective : Function.Bijective (targetToTatePreimage b q f) := by
  constructor
  · intro x y hxy
    apply Isogeny.Tate.integralEmbedding_injective q
    exact (GeometricIsogeny.geometricTateIsogenyEquiv b q f).symm.injective (congrArg Subtype.val hxy)
  · intro z
    obtain ⟨y, hy⟩ := z.property
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change (GeometricIsogeny.geometricTateIsogenyEquiv b q f).symm (1 ⊗ₜ[ℤ_[q]] y) = z.val
    change 1 ⊗ₜ[ℤ_[q]] y = GeometricIsogeny.geometricTateIsogenyEquiv b q f z.val at hy
    rw [hy, LinearEquiv.symm_apply_apply]

def targetTatePreimageEquiv : Add.schemeTateModule B.scheme (Over.mk b) q ≃ₗ[ℤ_[q]]
    Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom :=
  LinearEquiv.ofBijective (targetToTatePreimage b q f) (targetToTatePreimage_bijective b q f)

theorem targetTatePreimageEquiv_map (x : Add.schemeTateModule A.scheme (Over.mk b) q) :
    (targetTatePreimageEquiv b q f (Add.schemeTateMap A.scheme (Over.mk b) q f.hom x)).val =
      1 ⊗ₜ[ℤ_[q]] x := by
  change (GeometricIsogeny.geometricTateIsogenyEquiv b q f).symm
    (1 ⊗ₜ[ℤ_[q]] Add.schemeTateMap A.scheme (Over.mk b) q f.hom x) = _
  rw [← Lattices.rationalTateMap_integral]
  exact (GeometricIsogeny.geometricTateIsogenyEquiv b q f).symm_apply_apply _

def sourceInTatePreimage : Submodule ℤ_[q]
    (Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom) :=
  (Rational.integralTateImage A.scheme (Over.mk b) q).comap
    (Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom).subtype

theorem targetTatePreimageEquiv_range :
    (Add.schemeTateMap A.scheme (Over.mk b) q f.hom).range.map
      (targetTatePreimageEquiv b q f).toLinearMap = sourceInTatePreimage b q f := by
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (targetTatePreimageEquiv_map b q f x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨Add.schemeTateMap A.scheme (Over.mk b) q f.hom x, ⟨x, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (targetTatePreimageEquiv_map b q f x).trans hx

def tateCokernelEquivLatticeQuotient :
    (Add.schemeTateModule B.scheme (Over.mk b) q ⧸
      (Add.schemeTateMap A.scheme (Over.mk b) q f.hom).range) ≃ₗ[ℤ_[q]]
        (Rational.isogenyTatePreimage (T := Over.mk b) (q := q) f.hom ⧸ sourceInTatePreimage b q f) :=
  Submodule.Quotient.equiv _ _ (targetTatePreimageEquiv b q f) (targetTatePreimageEquiv_range b q f)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PreimageQuotient
