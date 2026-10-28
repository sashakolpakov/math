import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ReverseSides
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelQuotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision

/-! # Polarized Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! For an actual polarized q-power isogeny, the Tate cokernel is the
actual kernel on q-power torsion points. All reverse-map and evaluation
hypotheses of the exact-sequence calculation are proved here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u
variable {R : Type u} [CommRing R] {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {g N m : ℕ} {P Q : PEL.PELFamilyData R g N (Spec (.of k))}
  (q : ℕ) [Fact q.Prime] (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (δ : Fin g → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

def PELIsogenies.PELIsogeny.tateCokernelEquivTorsionKernel :
    (Add.schemeTateModule Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q ⧸
      (Add.schemeTateMap P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q e.isogeny.hom).range) ≃ₗ[ℤ_[q]]
      (Add.Tate.mapLevel q
        (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toAdditive m).ker := by
  let φ := (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toAdditive
  let d := e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq
  have hdf : d.comp (Add.Tate.map q φ) = (q : ℤ_[q]) ^ m • LinearMap.id := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact e.integralTateReverse_comp (𝟙 (Spec (.of k))) q δ hδ hq
  have hfd : (Add.Tate.map q φ).comp d = (q : ℤ_[q]) ^ m • LinearMap.id := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact e.comp_integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq
  exact KernelQuotient.Tate.cokernelEquivKernel q φ m d hdf hfd (GeometricDivision.geometricPoint_divisible P.abelian q)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
