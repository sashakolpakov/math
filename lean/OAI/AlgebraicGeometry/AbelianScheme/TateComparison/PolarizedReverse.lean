import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites

/-! # Polarized Reverse -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The source polarization and actual Poincare dual construct an
integral reverse map for a polarized isogeny, up to its multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N n : ℕ}
  {P Q : PEL.PELFamilyData R g N S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime]
  (e : PELIsogenies.PELIsogeny P Q n) (δ : Fin g → ℕ)
  (hδ : P.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

def PELIsogenies.PELIsogeny.integralTateReverse :
    Add.schemeTateModule Q.abelian.scheme (Over.mk b) q →ₗ[ℤ_[q]]
      Add.schemeTateModule P.abelian.scheme (Over.mk b) q :=
  (Polarization.polarizationTateEquiv b q P.polarizationMap δ hδ hq).symm.toLinearMap.comp
    ((Add.schemeTateMap Q.dual.abelian.scheme (Over.mk b) q e.dualHom).comp
      (Add.schemeTateMap Q.abelian.scheme (Over.mk b) q Q.polarizationMap.hom))

theorem PELIsogenies.PELIsogeny.integralTateReverse_comp :
    (e.integralTateReverse b q δ hδ hq).comp
      (Add.schemeTateMap P.abelian.scheme (Over.mk b) q e.isogeny.hom) = n • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f x) (e.tate_polarization (Over.mk b) q)
  change Add.schemeTateMap Q.dual.abelian.scheme (Over.mk b) q e.dualHom
      (Add.schemeTateMap Q.abelian.scheme (Over.mk b) q Q.polarizationMap.hom
        (Add.schemeTateMap P.abelian.scheme (Over.mk b) q e.isogeny.hom x)) =
      n • Add.schemeTateMap P.abelian.scheme (Over.mk b) q P.polarizationMap.hom x at h
  change (Polarization.polarizationTateEquiv b q P.polarizationMap δ hδ hq).symm
      (Add.schemeTateMap Q.dual.abelian.scheme (Over.mk b) q e.dualHom
        (Add.schemeTateMap Q.abelian.scheme (Over.mk b) q Q.polarizationMap.hom
          (Add.schemeTateMap P.abelian.scheme (Over.mk b) q e.isogeny.hom x))) = n • x
  rw [h, map_nsmul]
  exact congrArg (fun y => n • y)
    ((Polarization.polarizationTateEquiv b q P.polarizationMap δ hδ hq).symm_apply_apply x)

include δ hδ hq in
theorem PELIsogenies.PELIsogeny.multiplier_smul_mem_integralTateImage
    (z : Rational.rationalTateModule P.abelian.scheme (Over.mk b) q)
    (hz : z ∈ Rational.isogenyTatePreimage (T := Over.mk b) (q := q) e.isogeny.hom) :
    (n : ℤ_[q]) • z ∈ Rational.integralTateImage P.abelian.scheme (Over.mk b) q := by
  obtain ⟨y, hy⟩ := hz
  let f := Add.schemeTateMap P.abelian.scheme (Over.mk b) q e.isogeny.hom
  let d := e.integralTateReverse b q δ hδ hq
  have hd : (d.baseChange ℚ_[q]).comp (f.baseChange ℚ_[q]) = n • LinearMap.id := by
    rw [← LinearMap.baseChange_comp, PELIsogenies.PELIsogeny.integralTateReverse_comp]
    exact (map_nsmul (LinearMap.baseChangeHom ℤ_[q] ℚ_[q] _ _) n LinearMap.id).trans
      (congrArg (fun m => n • m) LinearMap.baseChange_id)
  refine ⟨d y, ?_⟩
  change 1 ⊗ₜ[ℤ_[q]] (d y) = (n : ℤ_[q]) • z
  have hdz := congrArg (fun m => m z) hd
  change d.baseChange ℚ_[q] (Rational.rationalTateMap (T := Over.mk b) (q := q) e.isogeny.hom z) = n • z at hdz
  change 1 ⊗ₜ[ℤ_[q]] y = Rational.rationalTateMap (T := Over.mk b) (q := q) e.isogeny.hom z at hy
  rw [← hy] at hdz
  simpa only [LinearMap.baseChange_tmul, Nat.cast_smul_eq_nsmul] using hdz

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
