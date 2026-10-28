import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedKernelGroups
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision

/-! # Geometric Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The whole geometric kernel of an actual polarized q-isogeny is killed
by its multiplier. Equal polarization types rule out every prime-to-q
part; this is stronger than a statement about its chosen Tate block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (n : ℕ) [NeZero n]

theorem GeometricKernel.geometricPowerKernel_finite :
    Finite (powMonoidHom n : A.Points (Over.mk (𝟙 (Spec (.of k)))) →*
      A.Points (Over.mk (𝟙 (Spec (.of k))))).ker := by
  let e := GeometricDivision.multiplicationIsogeny A n
  have : Finite (e.kernelAt (Over.mk (𝟙 (Spec (.of k))))) :=
    FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite e (𝟙 (Spec (.of k)))
  let i : (powMonoidHom n : A.Points (Over.mk (𝟙 (Spec (.of k)))) →*
      A.Points (Over.mk (𝟙 (Spec (.of k))))).ker →
      e.kernelAt (Over.mk (𝟙 (Spec (.of k)))) := fun x => ⟨x.val, by
    change x.val ≫ (𝟙 A.scheme) ^ n = 1
    rw [MonObj.comp_pow, Category.comp_id]
    exact x.property⟩
  apply Finite.of_injective i
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : e.kernelAt (Over.mk (𝟙 (Spec (.of k)))) => z.val) h

theorem GeometricKernel.geometricPower_surjective :
    Function.Surjective (powMonoidHom n : A.Points (Over.mk (𝟙 (Spec (.of k)))) →*
      A.Points (Over.mk (𝟙 (Spec (.of k))))) := by
  intro x
  obtain ⟨y, hy⟩ := GeometricDivision.geometricPoint_divisible A n (Additive.ofMul x)
  exact ⟨y.toMul, congrArg Additive.toMul hy⟩

variable {R : Type u} [CommRing R] {N q m : ℕ} [Fact q.Prime]
  {P Q : PEL.PELFamilyData R g N (Spec (.of k))} (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
  (hQ : Q.polarizationMap.HasPolarizationType δ)

omit [CharZero k] [IsAlgClosed k] [Fact q.Prime] in
theorem PELIsogenies.PELIsogeny.geometricPoints_polarization :
    ((Q.dual.abelian.mapPoints P.dual.abelian e.dualHom (Over.mk (𝟙 (Spec (.of k))))).comp
      (Q.abelian.mapPoints Q.dual.abelian Q.polarizationMap.hom (Over.mk (𝟙 (Spec (.of k)))))).comp
      (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))) =
    (P.abelian.mapPoints P.dual.abelian P.polarizationMap.hom (Over.mk (𝟙 (Spec (.of k))))).comp
      (powMonoidHom (q ^ m)) := by
  apply MonoidHom.ext
  intro x
  change (x ≫ e.isogeny.hom) ≫ Q.polarizationMap.hom ≫ e.dualHom =
    (x ^ (q ^ m)) ≫ P.polarizationMap.hom
  rw [Category.assoc, e.polarization, MonObj.comp_pow, MonObj.pow_comp]

include hP hQ in
theorem PELIsogenies.PELIsogeny.geometricKernel_killed (hq : Nat.Coprime q (∏ i, δ i))
    (x : P.abelian.Points (Over.mk (𝟙 (Spec (.of k)))))
    (hx : x ≫ e.isogeny.hom = 1) : x ^ (q ^ m) = 1 := by
  let f := P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))
  let p := P.abelian.mapPoints P.dual.abelian P.polarizationMap.hom (Over.mk (𝟙 (Spec (.of k))))
  let r := Q.abelian.mapPoints Q.dual.abelian Q.polarizationMap.hom (Over.mk (𝟙 (Spec (.of k))))
  let d := Q.dual.abelian.mapPoints P.dual.abelian e.dualHom (Over.mk (𝟙 (Spec (.of k))))
  have : Finite p.ker := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite P.polarizationMap _
  have := GeometricKernel.geometricPowerKernel_finite P.abelian (q ^ m)
  have hp : Nat.card p.ker = (∏ i, δ i) ^ 2 :=
    Polarization.polarization_kernelCard (𝟙 (Spec (.of k))) P.polarizationMap δ hP
  have hr : Nat.card r.ker = (∏ i, δ i) ^ 2 :=
    Polarization.polarization_kernelCard (𝟙 (Spec (.of k))) Q.polarizationMap δ hQ
  exact PolarizedKernelGroups.KernelCardinality.polarized_kernel_killed f p r d q m
    (FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective e.isogeny _)
    (FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective Q.polarizationMap _)
    (GeometricKernel.geometricPower_surjective P.abelian (q ^ m))
    (hp.trans hr.symm) e.geometricPoints_polarization (hp.symm ▸ hq.pow_right 2) x hx

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
