import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntegralDegree
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers

/-! # Isogeny Torsion Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IsogenyTorsionRank

noncomputable section

/-! Isogenous abelian varieties have equal scheme-theoretic torsion orders. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- Over an algebraically closed field, a smooth proper connected group is integral. -/
theorem abelianGroup_isIntegral
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] : IsIntegral A.left := by
  have : IrreducibleSpace A.left :=
    Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : IsReduced A.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field A.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced A.left

/-- Multiplication degrees agree across an isogeny for every n with finite multiplication.
No coprimality or invertibility assumption on n is used. -/
theorem multiplication_finrank_eq_of_isogeny
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [IsFinite ((𝟙 B : B ⟶ B) ^ n).left]
    (s : Spec (.of k)) :
    ((𝟙 A : A ⟶ A) ^ n).left.finrank (η[A].left s) =
      ((𝟙 B : B ⟶ B) ^ n).left.finrank (η[B].left s) := by
  have : IsIntegral A.left := abelianGroup_isIntegral A
  have : IsIntegral B.left := abelianGroup_isIntegral B
  have ha := MultiplicationFlat.Construction.Multiplication.surjective_flat_power_of_isFinite A n
  have hb := MultiplicationFlat.Construction.Multiplication.surjective_flat_power_of_isFinite B n
  have : Surjective ((𝟙 A : A ⟶ A) ^ n).left := ha.1
  have : Flat ((𝟙 A : A ⟶ A) ^ n).left := ha.2
  have : Flat ((𝟙 B : B ⟶ B) ^ n).left := hb.2
  have : LocallyOfFinitePresentation ((𝟙 B : B ⟶ B) ^ n).left :=
    MultiplicationFlat.Construction.Multiplication.locallyOfFinitePresentation_overEnd B _
  have : LocallyOfFinitePresentation f.left := by
    have h : LocallyOfFinitePresentation (f.left ≫ B.hom) := by rw [f.w]; infer_instance
    exact Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType h inferInstance
  have h : ((𝟙 A : A ⟶ A) ^ n) ≫ f = f ≫ ((𝟙 B : B ⟶ B) ^ n) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hr := IntegralDegree.Construction.Schemes.endomorphism_finrank_eq_of_commuting f.left
    ((𝟙 A : A ⟶ A) ^ n).left ((𝟙 B : B ⟶ B) ^ n).left
    (congrArg Over.Hom.left h) (η[A].left s)
  have hη : η[A] ≫ f = η[B] := IsMonHom.one_hom f
  have hηs : f.left (η[A].left s) = η[B].left s :=
    congrArg (fun v : 𝟙_ (Over (Spec (.of k))) ⟶ B => v.left s) hη
  rwa [hηs] at hr

/-- The actual full multiplication kernels have the same finite-flat rank across an isogeny. -/
theorem torsionKernel_finrank_eq_of_isogeny
    {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [IsFinite ((𝟙 B : B ⟶ B) ^ n).left]
    (s : Spec (.of k)) :
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A : A ⟶ A) ^ n)).hom.finrank s =
      (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 B : B ⟶ B) ^ n)).hom.finrank s := by
  have := MultiplicationFlat.Construction.Multiplication.flat_power_of_isFinite A n
  have := MultiplicationFlat.Construction.Multiplication.flat_power_of_isFinite B n
  rw [Picard.Homomorphisms.FrobeniusKernelRank.Construction.kernelScheme_finrank, Picard.Homomorphisms.FrobeniusKernelRank.Construction.kernelScheme_finrank]
  exact multiplication_finrank_eq_of_isogeny A B f n s

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IsogenyTorsionRank
