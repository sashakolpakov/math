import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.GlobalFunctions

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.Torsion.Construction

noncomputable section

/-! Prime-to-characteristic torsion cannot occur in the actual group-homomorphism group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B] [IsCommMonObj B]
  [IsProper A.hom] [GeometricallyIntegral A.hom] [IsProper B.hom] [Smooth B.hom]

/-- A group homomorphism annihilated by an integer invertible in the field is zero.
It factors through the actual finite torsion kernel, and proper global functions
make that factorization constant at the identity. -/
theorem groupHom_eq_one_of_pow_eq_one (f : A ⟶ B) [IsMonHom f]
    (n : ℕ) (hn : (n : K) ≠ 0) (hf : f ^ n = 1) : f = 1 := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme B n).hom := (Multiplication.Construction.torsionScheme_finite_etale B n hn).1
  have : IsAffine (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme B n).left :=
    isAffine_of_isAffineHom (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme B n).hom
  let t := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n f hf
  have ht := Proper.GlobalFunctions.Construction.properIntegral_to_affine_constant A.hom (η[A]).left (η[A]).w t.left
  have h := congrArg (fun g => g ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι B n).left) ht
  have htf : t.left ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι B n).left = f.left :=
    congrArg (fun g : A ⟶ B => g.left) (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n f hf)
  have hunit : (η[A]).left ≫ f.left = (η[B]).left :=
    congrArg (fun g : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B => g.left)
      (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  change f.left = A.hom ≫ (η[B]).left
  simpa only [Category.assoc, htf, hunit] using h

variable (A) [IsCommMonObj A] [Smooth A.hom]

/-- Multiplication by a nonzero field integer is injective on the actual endomorphism group. -/
theorem algebraicEnd_nsmul_eq_zero (n : ℕ) (hn : (n : K) ≠ 0)
    (f : Endomorphisms.Construction.AlgebraicEnd A) (hf : n • f = 0) : f = 0 := by
  have hf' : f.toMul ^ n = 1 := congrArg Additive.toMul hf
  have h : f.toMul.hom.hom ^ n = 1 := by
    simpa only [Grp.Hom.hom_pow, Mon.Hom.hom_pow, Grp.Hom.hom_one, Mon.Hom.hom_one] using
      congrArg (fun g : Grp.mk A ⟶ Grp.mk A => g.hom.hom) hf'
  have hz := groupHom_eq_one_of_pow_eq_one f.toMul.hom.hom n hn h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact hz

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.Torsion.Construction
