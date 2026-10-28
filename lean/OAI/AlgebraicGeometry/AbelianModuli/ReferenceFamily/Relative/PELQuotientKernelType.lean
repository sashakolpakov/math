import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PELClassifyingTarget

/-! # PEL Quotient Kernel Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELQuotientKernelType

noncomputable section

/-! A relative PEL quotient has exactly the original subgroup's
geometric kernel type and exponent, using the literal pullback point
equivalence and the quotient's all-test kernel theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} {A : PEL.Objects.PELObject P iota N T}
    {Q : Over T.left} {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme Q}
    (h : AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)

def relativePELQuotientKernelEquiv (X : Over Q.left) :
    h.quotient.isogeny.kernelAt X ≃*
      F.points ((Over.map Q.hom).obj X) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q X) where
  toFun x := ⟨A.polarized.abelian.baseChangePointsMulEquiv Q.hom X x.val,
    (h.kernel X x.val).mp x.property⟩
  invFun x := ⟨(A.polarized.abelian.baseChangePointsMulEquiv Q.hom X).symm x.val, by
    apply (h.kernel X _).mpr
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext
    ((A.polarized.abelian.baseChangePointsMulEquiv Q.hom X).symm_apply_apply x.val)
  right_inv x := Subtype.ext
    ((A.polarized.abelian.baseChangePointsMulEquiv Q.hom X).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext
    ((A.polarized.abelian.baseChangePointsMulEquiv Q.hom X).map_mul x.val y.val)

theorem relativePELQuotient_kernel_moduleType (M : Type) [AddCommGroup M]
    (hM : F.HasModuleType M) :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel h.quotient.isogeny.hom).HasModuleType M := by
  intro k _ _ b t
  obtain ⟨e⟩ := hM k (b ≫ Q.hom) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q (Over.mk b))
  exact ⟨(relativePELQuotientKernelEquiv h (Over.mk b)).trans e⟩

theorem relativePELQuotient_kernel_killed (hkilled : F.KilledBy n)
    (X : Over Q.left) (x : X ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme h.quotient.isogeny.hom) :
    x ^ n = 1 := by
  let f := h.quotient.isogeny.hom
  let a := x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f
  have ha : a ≫ f = 1 := by
    rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]
  have hb := (h.kernel X a).mp ha
  have hpow : a ^ n = 1 := by
    apply (A.polarized.abelian.baseChangePointsMulEquiv Q.hom X).injective
    rw [map_pow, map_one]
    exact hkilled _ _ _ hb
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact hpow

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELQuotientKernelType
