import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Parameter Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterKernel.Construction

noncomputable section

/-! Isogenies of abelian schemes have finite presentation. Their
scheme-theoretic kernel exponent persists on every base-changed test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem abelianIsogeny_locallyOfFinitePresentation : LocallyOfFinitePresentation f.hom.left :=
  Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType
    (show LocallyOfFinitePresentation (f.hom.left ≫ B.scheme.hom) from
      f.hom.w.symm ▸ inferInstance) inferInstance

theorem isogeny_kernelPoint_pow_of_kernelScheme (n : ℕ)
    (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ≫ f.hom = 1) : x ^ n = 1 := by
  have h := congrArg (fun y : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom => y ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom)
    (hk T (Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift f.hom x hx))
  rwa [MonObj.pow_comp, Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift_inclusion, MonObj.one_comp] at h

include f in
theorem isogeny_baseChange_kernelPoint_pow (n : ℕ)
    (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
    (s : S' ⟶ S) (T : Over S') (x : T ⟶ (A.pullback s).scheme)
    (hx : x ≫ (f.pullback s).hom = 1) : x ^ n = 1 := by
  apply (A.baseChangePointsMulEquiv s T).injective
  rw [map_pow, map_one]
  apply isogeny_kernelPoint_pow_of_kernelScheme f n hk
  change A.baseChangePointsEquiv s T x ≫ f.hom = 1
  rw [← AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom s T x]
  change B.baseChangePointsMulEquiv s T (x ≫ (f.pullback s).hom) = 1
  rw [hx, map_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterKernel.Construction
