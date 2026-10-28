import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CoefficientRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientRefinementTransport

/-! # Refinement Reference Base -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementReferenceBase.Construction

noncomputable section

/-! Ambient coefficient refinements preserve the original ground algebra. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {H B R : Type u} [CommRing k] [CommRing H] [CommRing B] [CommRing R]
  [Algebra k H] [Algebra k B] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra.Smooth k R]

/-- The actual ambient refinement is an étale map over the original ground
ring. Its coordinate, coefficient map, smoothness, and retraction square are
all retained, so it can be used in the next recursive coefficient step. -/
theorem exists_etale_line_original_base_refinement
    (φ : H →ₐ[k] B) (hφ : φ.toRingHom.Etale)
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) :
    ∃ (V : CommRingCat.{u}) (_ : Algebra k V) (_ : Algebra B V) (_ : Algebra B[X] V),
      IsScalarTower k B V ∧ IsScalarTower B B[X] V ∧ Algebra.Etale B[X] V ∧ Algebra.Smooth k V ∧
      ∃ f : R →ₐ[k] V, f.toRingHom.Etale ∧
        f (algebraMap H[X] R X) = algebraMap B[X] V X ∧
        (∀ h : H, f (algebraMap H R h) = algebraMap B V (φ h)) ∧
        ∃ e' : (V ⧸ Ideal.span {f (algebraMap H[X] R X)}) ≃ₐ[B] B,
          e'.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {f (algebraMap H[X] R X)})).comp f.toRingHom) =
            φ.toRingHom.comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}))) := by
  let : Algebra H B := φ.toRingHom.toAlgebra
  let : Algebra.Etale H B := RingHom.etale_algebraMap.mp hφ
  obtain ⟨V, cV, aBV, aBPV, ht, he, g, hg, hcoord, hcoeff, e', hcomm⟩ :=
    CoefficientRefinement.Construction.exists_etale_line_coefficient_refinement (B := B) e
  let : Algebra k V := ((algebraMap B V).comp (algebraMap k B)).toAlgebra
  let : IsScalarTower k B V := IsScalarTower.of_algebraMap_eq' rfl
  let f : R →ₐ[k] V := { g with
    commutes' x := by
      change g (algebraMap k R x) = algebraMap k V x
      rw [IsScalarTower.algebraMap_apply k H R, hcoeff]
      change algebraMap B V (φ (algebraMap k H x)) = algebraMap k V x
      rw [φ.commutes]
      rfl }
  have hbase : g.comp (algebraMap k R) = algebraMap k V := RingHom.ext f.commutes
  have hgsm : g.Smooth := ((RingHom.etale_iff_formallyUnramified_and_smooth g).mp hg).2
  have hsm := RingHom.Smooth.comp (RingHom.smooth_algebraMap.mpr (inferInstance : Algebra.Smooth k R)) hgsm
  rw [hbase] at hsm
  let : Algebra.Smooth k V := RingHom.smooth_algebraMap.mp hsm
  exact ⟨.of V, inferInstance, aBV, aBPV, inferInstance, ht, he, inferInstance,
    f, hg, hcoord, hcoeff, e', hcomm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementReferenceBase.Construction
