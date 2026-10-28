import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfPowerComplement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Finite
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction

/-! # Scalar Complement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ScalarComplement.Construction

noncomputable section

/-! The actual scalar complement of an isogeny is itself an isogeny,
and its scheme-theoretic kernel has the same exponent bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hf : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)

include hn hf in
set_option backward.isDefEq.respectTransparency false in
theorem exists_isogeny_scalar_complement
    {k : Type u} [Field k] [CharZero k] (base : S ⟶ Spec (.of k)) :
    ∃ v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A,
      f.hom ≫ v.hom = (𝟙 A.scheme) ^ n ∧ v.hom ≫ f.hom = (𝟙 B.scheme) ^ n ∧
      ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme v.hom), x ^ n = 1 := by
  obtain ⟨r, hr, hfr, hrf⟩ := FppfPowerComplement.Construction.exists_fppf_power_complement f.hom n
    (ParameterKernel.Construction.isogeny_kernelPoint_pow_of_kernelScheme f n hf)
  have : IsMonHom r := hr
  have hfin := (Multiplication.Construction.multiplication_finite_flat B.scheme n
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := B.scheme) base n hn Torsion.Construction.verified_TorsionQuotientInput).1).1
  have : IsFinite (r.left ≫ f.hom.left) := by
    change IsFinite (r ≫ f.hom).left
    rw [hrf]
    exact hfin
  have : IsFinite r.left := IsFinite.of_comp r.left f.hom.left
  let v := Relative.Finite.Construction.relativeFiniteAbelianHomIsogeny B A r
  refine ⟨v, hfr, hrf, ?_⟩
  intro T x
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion v.hom)).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact FppfPowerComplement.Construction.powerComplement_kernel_torsion f.hom v.hom n hrf T (x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion v.hom)
    (by rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one])

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ScalarComplement.Construction
