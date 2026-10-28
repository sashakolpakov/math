import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.Torsion
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding

/-! # Positive Multiplication -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication

noncomputable section

/-! The proved cube identity makes every positive multiplication finite,
including characteristic-power multiplication. The actual endomorphism
group consequently has no nonzero integer torsion. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.Obj

namespace Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem multiplication_positive_isFinite (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 A : A ⟶ A) ^ n).left :=
  Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.isFinite A (CubeIdentity.Construction.lineBundle_isCubical A) n hn

theorem torsionScheme_positive_finite (n : ℕ) (hn : 0 < n) :
    IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom :=
  MorphismProperty.of_isPullback (AbelianScheme.TorsionQuotient.Left.TorsionPullback.isPullback_left A n)
    (multiplication_positive_isFinite A n hn)

theorem groupHom_eq_one_of_positive_pow
    {B : Over (Spec (CommRingCat.of K))} [GrpObj B]
    [IsProper B.hom] [GeometricallyIntegral B.hom]
    (f : B ⟶ A) [IsMonHom f] (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) : f = 1 := by
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom := torsionScheme_positive_finite A n hn
  have : IsAffine (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).left :=
    isAffine_of_isAffineHom (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom
  let t := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n f hf
  have ht := Proper.GlobalFunctions.Construction.properIntegral_to_affine_constant B.hom (η[B]).left (η[B]).w t.left
  have h := congrArg (fun g => g ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left) ht
  have htf : t.left ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left = f.left :=
    congrArg (fun g : B ⟶ A => g.left) (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n f hf)
  have hunit : (η[B]).left ≫ f.left = (η[A]).left :=
    congrArg (fun g : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A => g.left)
      (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  change f.left = B.hom ≫ (η[A]).left
  simpa only [Category.assoc, htf, hunit] using h

theorem algebraicEnd_positive_nsmul_eq_zero (n : ℕ) (hn : 0 < n)
    (f : Endomorphisms.Construction.AlgebraicEnd A) (hf : n • f = 0) : f = 0 := by
  have hf' : f.toMul ^ n = 1 := congrArg Additive.toMul hf
  have h : f.toMul.hom.hom ^ n = 1 := by
    simpa only [Grp.Hom.hom_pow, Mon.Hom.hom_pow, Grp.Hom.hom_one, Mon.Hom.hom_one] using
      congrArg (fun g : Grp.mk A ⟶ Grp.mk A => g.hom.hom) hf'
  have hz := groupHom_eq_one_of_positive_pow A f.toMul.hom.hom n hn h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact hz

omit [IsAlgClosed K] in
/-- The actual endomorphism group over any field has no positive-integer torsion. -/
theorem algebraicEnd_nsmul_eq_zero_of_positive (n : ℕ) (hn : 0 < n)
    (f : Endomorphisms.Construction.AlgebraicEnd A) (hf : n • f = 0) : f = 0 := by
  let B := Geometric.Frobenius.Construction.geometricFiberOver K A
  have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : GeometricallyIntegral B.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A)) := Endomorphisms.Construction.algebraicEndRing _
  let : AddMonoid (Endomorphisms.Construction.AlgebraicEnd B) := (Endomorphisms.Construction.algebraicEndRing B).toAddMonoid
  let φ : Endomorphisms.Construction.AlgebraicEnd A →+* Endomorphisms.Construction.AlgebraicEnd B := Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange K A
  have hφ : n • φ f = 0 := by rw [← map_nsmul, hf, map_zero]
  have hz := algebraicEnd_positive_nsmul_eq_zero B n hn (φ f) hφ
  apply Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange_injective K A
  exact hz.trans (map_zero φ).symm

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PositiveMultiplication
