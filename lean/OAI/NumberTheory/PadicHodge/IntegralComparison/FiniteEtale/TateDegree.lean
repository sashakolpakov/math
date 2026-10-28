import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.KernelDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.TateFiniteKernelNorm
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerOrbitEq

/-! # Tate Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TateDegree

noncomputable section

/-! The native Tate determinant of a finite étale group endomorphism
has the prime-adic norm of its actual geometric degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.KernelDegree

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]

omit [IsCommMonObj A] in
theorem pointAction_surjective (f : A ⟶ A) [IsMonHom f]
    [Surjective f.left] [LocallyOfFiniteType f.left] :
    Function.Surjective (KernelDegree.pointAction A f) := by
  intro x
  obtain ⟨y, hy⟩ := AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift.Construction.exists_rationalPoint_lift f.left x.toMul.left
  have yw : y ≫ A.hom = 𝟙 _ := by
    rw [← f.w, ← Category.assoc, hy]
    exact x.toMul.w
  refine ⟨Additive.ofMul (Over.homMk y yw), ?_⟩
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  exact hy

omit [IsCommMonObj A] in
theorem pointAction_kernel_finite (f : A ⟶ A) [IsMonHom f] [IsFinite f.left] :
    Finite (KernelDegree.pointAction A f).ker := by
  let B := AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject f
  let : IsFinite B.hom := AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f
  let : Finite (𝟙_ (Over (Spec (.of k))) ⟶ B) :=
    AlgebraicGeometry.Quotients.FiniteDescent.PowerOrbitEq.Construction.PowerOrbit.finite_fieldPoints B (𝟙 _)
  exact Finite.of_equiv _ ((AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f
    (𝟙_ (Over (Spec (.of k))))).trans (KernelDegree.kernelAdditiveEquiv A f))

variable [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

include hp

theorem determinant_valuation (f : A ⟶ A) [IsMonHom f]
    [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p (KernelDegree.pointAction A f)).det.valuation =
      (f.left.residueDegree (genericPoint A.left)).factorization p := by
  let : Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p (Geometric.TateModule.Points A) 1) := Geometric.TateModule.torsion_finite A p hp 1
  let : Finite (KernelDegree.pointAction A f).ker := pointAction_kernel_finite A f
  rw [← KernelDegree.kernel_card A f]
  exact TateFiniteKernelNorm.determinant_valuation p (KernelDegree.pointAction A f)
    (pointAction_surjective A f) (Geometric.TateModule.divisible A p hp)

theorem determinant_norm (f : A ⟶ A) [IsMonHom f]
    [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    ‖((AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p (KernelDegree.pointAction A f)).det : ℚ_[p])‖ =
      ‖(f.left.residueDegree (genericPoint A.left) : ℚ_[p])‖ := by
  let : Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p (Geometric.TateModule.Points A) 1) := Geometric.TateModule.torsion_finite A p hp 1
  let : Finite (KernelDegree.pointAction A f).ker := pointAction_kernel_finite A f
  rw [← KernelDegree.kernel_card A f]
  exact TateFiniteKernelNorm.determinant_norm p (KernelDegree.pointAction A f)
    (pointAction_surjective A f) (Geometric.TateModule.divisible A p hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TateDegree
