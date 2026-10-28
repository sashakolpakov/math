import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Finiteness

/-! # Essential Smooth Flat -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EssentialSmoothFlat.BundleCycles

noncomputable section

/-! # LineBundleCycles: formally smooth essentially finite type algebras over a Noetherian base are flat -/

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.EssFiniteType A B] [Algebra.FormallySmooth A B]

theorem formallySmooth_flat_of_essFiniteType : Module.Flat A B := by
  let C := Algebra.EssFiniteType.subalgebra A B
  let M := Algebra.EssFiniteType.submonoid A B
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := C)).mp inferInstance
  let P := MvPolynomial (Fin n) A
  let N : Submonoid P := M.comap f.toRingHom.toMonoidHom
  have hN : N.map f.toRingHom = M := by
    rw [← Submonoid.map_coe_toMonoidHom]
    exact Submonoid.map_comap_eq_of_surjective hf M
  have hloc : IsLocalization (N.map f.toRingHom) B := by
    rw [hN]
    exact Algebra.EssFiniteType.isLocalization A B
  let L := Localization N
  let q : L →+* B := IsLocalization.map B f.toRingHom N.le_comap_map
  have hq : Function.Surjective q := IsLocalization.map_surjective_of_surjective N L B hf
  let qA : L →ₐ[A] B := {
    toRingHom := q
    commutes' := by
      intro a
      change q (algebraMap A L a) = algebraMap A B a
      rw [IsScalarTower.algebraMap_apply A P L, IsLocalization.map_eq]
      exact (congrArg (algebraMap C B) (f.commutes a)).trans
        (IsScalarTower.algebraMap_apply A C B a).symm }
  have : IsNoetherianRing P := inferInstance
  have : IsNoetherianRing L := IsLocalization.isNoetherianRing N L inferInstance
  have : Module.Flat A P := Module.Flat.of_free
  have : Module.Flat A L := Module.Flat.trans A P L
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing qA hq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EssentialSmoothFlat.BundleCycles
