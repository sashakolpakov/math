import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Form Basis Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormBasisTransport

noncomputable section

/-!
# IntegralComparison: transport of bases of actual divided-power differential forms

A divided-power algebra equivalence transports a form basis across its
actual semilinear pullback map. The resulting basis has an explicit
formula, preserving the differential symbols needed for linearization.
-/

open _root_.CategoryTheory

universe u v

variable (R A C : Type u) [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
  (I : Ideal A) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)
  (e : A ≃ₐ[R] C) (he : DividedPowers.IsDPMorphism δ ε e.toRingHom)
  (hi : DividedPowers.IsDPMorphism ε δ e.symm.toRingHom)
  (n : ℕ) {ι : Type v} (b : Module.Basis ι A (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n))

def basis : Module.Basis ι C (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R C J ε n) := by
  letI : Module C (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) :=
    Module.compHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) e.symm.toRingHom
  let g : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n ≃ₗ[C] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R C J ε n :=
    { (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of R A) (B := CommAlgCat.of R C) e he hi n).toEquiv with
      map_add' := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv
        (A := CommAlgCat.of R A) (B := CommAlgCat.of R C) e he hi n).map_add
      map_smul' c ω := by
        have h := AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul (CommAlgCat.ofHom e.toAlgHom) he n (e.symm c) ω
        change _ = e (e.symm c) • _ at h
        rw [AlgEquiv.apply_symm_apply] at h
        exact h }
  exact (b.mapCoeffs e.toRingEquiv (fun a ω => by
    change e.symm (e a) • ω = a • ω
    rw [AlgEquiv.symm_apply_apply])).map g

theorem basis_apply (i : ι) : basis R A C I δ J ε e he hi n b i =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom e.toAlgHom) he n (b i) := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.mapCoeffs_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormBasisTransport
