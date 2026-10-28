import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.KernelCardinality
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny

/-! # Polarized Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizedKernels.Construction

noncomputable section

/-! Polarization controls the full geometric kernel, including torsion
away from q. Together with the intrinsic Tate comparison this identifies
all geometric kernel points of the actual PEL isogenies. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K R : Type} [Field K] [CharZero K] [CommRing R]
  {S : Scheme} {g N q h : ℕ}

def abelianMultiplierIsogeny (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (base : S ⟶ Spec (.of K)) (n : ℕ) (hn : n ≠ 0) : B.Isogeny B := by
  have hh := ScalarIsogeny.Construction.abelian_multiplier_finite_etale_surjective B n
    (ScalarIsogeny.Construction.nat_unit_on_charZero_scheme base n hn)
  have := hh.1
  have := hh.2.1
  have := hh.2.2
  refine ⟨(𝟙 B.scheme) ^ n, ?_, inferInstance, inferInstance, inferInstance⟩
  rw [← Scalar.Construction.scalar_natCast_schemeMap]
  infer_instance

theorem pelIsogeny_geometricKernel_isPGroup
    (A B : TateComparison.PEL.PELFamilyData R g N S) (base : S ⟶ Spec (.of K))
    (δ : Fin g → ℕ) (hA : A.polarizationMap.HasPolarizationType δ)
    (hB : B.polarizationMap.HasPolarizationType δ)
    (q : ℕ) [Fact q.Prime] (h : ℕ) (f : TateComparison.PELIsogenies.PELIsogeny A B (q ^ h))
    {k : Type} [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S) :
    IsPGroup q (f.isogeny.kernelAt (Over.mk t)) := by
  let T := Over.mk t
  let fp := A.abelian.mapPoints B.abelian f.isogeny.hom T
  let ap := A.abelian.mapPoints A.dual.abelian A.polarizationMap.hom T
  let bp := B.abelian.mapPoints B.dual.abelian B.polarizationMap.hom T
  let dp := B.dual.abelian.mapPoints A.dual.abelian f.dualHom T
  let m := abelianMultiplierIsogeny A.dual.abelian base (q ^ h)
    (pow_ne_zero h (Fact.out : q.Prime).ne_zero)
  let mp := A.dual.abelian.mapPoints A.dual.abelian m.hom T
  have : Finite ap.ker := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite A.polarizationMap t
  have : Finite mp.ker := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite m t
  have hm (x : A.dual.abelian.Points T) : mp x = x ^ (q ^ h) := by
    change x ≫ (𝟙 A.dual.abelian.scheme) ^ (q ^ h) = _
    rw [MonObj.comp_pow, Category.comp_id]
  have hcard : Nat.card ap.ker = Nat.card bp.ker :=
    (Nat.card_congr (hA.geometricKernel k t).some.toEquiv).trans
      (Nat.card_congr (hB.geometricKernel k t).some.toEquiv).symm
  have hpol : dp.comp (bp.comp fp) = mp.comp ap := by
    apply MonoidHom.ext
    intro x
    change ((x ≫ f.isogeny.hom) ≫ B.polarizationMap.hom) ≫ f.dualHom =
      mp (x ≫ A.polarizationMap.hom)
    rw [hm, Category.assoc, Category.assoc, f.polarization, MonObj.comp_pow]
  exact KernelCardinality.Construction.kernel_isPGroup_of_polarization q fp bp dp ap mp
    (FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective f.isogeny t)
    (FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective A.polarizationMap t)
    hcard hpol (fun x => ⟨h, Subtype.ext ((hm x.val).symm.trans x.property)⟩)

/-- The Tate comparison now identifies the entire geometric kernels,
without assuming a torsion bound or omitting the primes away from q. -/
theorem pelIsogeny_geometricKernel_eq_of_TatePreimage
    (A B C : TateComparison.PEL.PELFamilyData R g N S) (base : S ⟶ Spec (.of K))
    (δ : Fin g → ℕ) (hA : A.polarizationMap.HasPolarizationType δ)
    (hB : B.polarizationMap.HasPolarizationType δ)
    (hC : C.polarizationMap.HasPolarizationType δ)
    (q : ℕ) [Fact q.Prime] (h h' : ℕ)
    (f : TateComparison.PELIsogenies.PELIsogeny A B (q ^ h)) (e : TateComparison.PELIsogenies.PELIsogeny A C (q ^ h'))
    {k : Type} [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    (hpre : TateComparison.Rational.isogenyTatePreimage (T := Over.mk t) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk t) (q := q) e.isogeny.hom)
    (x : Over.mk t ⟶ A.abelian.scheme) :
    x ≫ f.isogeny.hom = 1 ↔ x ≫ e.isogeny.hom = 1 := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := pelIsogeny_geometricKernel_isPGroup A B base δ hA hB q h f t ⟨x, hx⟩
    exact (GeometricKernels.Construction.geometric_kernel_eq_on_torsion A.abelian B.abelian C.abelian base q t
      f.isogeny.hom e.isogeny.hom hpre n x (congrArg Subtype.val hn)).mp hx
  · intro hx
    obtain ⟨n, hn⟩ := pelIsogeny_geometricKernel_isPGroup A C base δ hA hC q h' e t ⟨x, hx⟩
    exact (GeometricKernels.Construction.geometric_kernel_eq_on_torsion A.abelian B.abelian C.abelian base q t
      f.isogeny.hom e.isogeny.hom hpre n x (congrArg Subtype.val hn)).mpr hx

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizedKernels.Construction
