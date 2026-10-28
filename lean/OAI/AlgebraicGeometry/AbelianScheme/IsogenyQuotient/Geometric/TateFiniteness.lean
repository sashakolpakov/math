import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group

/-! # Tate Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness.Construction

noncomputable section

/-!
Finite generation of geometric Tate modules over an arbitrary source
base follows from TorsionQuotient's finite torsion and geometric division. All points
are morphisms from the original geometric point to the original family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem finite_over_geometric_points {S : Scheme.{u}} (H : Over S) [IsFinite H.hom]
    (k : Type u) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S) :
    Finite (Over.mk b ⟶ H) := by
  have := FrobeniusKernel.GeometricIsogeny.Construction.finite_geometric_lifts H.hom b
  let f : (Over.mk b ⟶ H) → {x : Spec (.of k) ⟶ H.left // x ≫ H.hom = b} :=
    fun x => ⟨x.left, x.w⟩
  exact Finite.of_injective f (fun x y hxy => Over.OverMorphism.ext (congrArg Subtype.val hxy))

variable {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
  (base : S ⟶ Spec (.of K)) {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (k : Type u) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime]

include base in
theorem geometricTorsion_finite_from_TorsionQuotient (n : ℕ) :
    Finite (TateComparison.Add.Tate.torsion q (Additive (Over.mk b ⟶ A.scheme)) n) := by
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme (q ^ n)).hom :=
    (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient base (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) Torsion.Construction.verified_TorsionQuotientInput).1
  have := finite_over_geometric_points (TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme (q ^ n)) k b
  let f : TateComparison.Add.Tate.torsion q (Additive (Over.mk b ⟶ A.scheme)) n →
      (Over.mk b ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme (q ^ n)) := fun x =>
    TorsionQuotient.SubgroupFunctor.torsionLift (q ^ n) x.val.toMul (by
      have hx := congrArg Additive.toMul x.property
      simpa only [toMul_nsmul, toMul_zero] using hx)
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply Additive.toMul.injective
  have he := congrArg (fun a => a ≫ TorsionQuotient.SubgroupFunctor.torsionι A.scheme (q ^ n)) hxy
  simpa only [f, TorsionQuotient.SubgroupFunctor.torsionLift_ι] using he

include base in
theorem geometricTate_finite_from_TorsionQuotient : Module.Finite ℤ_[q]
    (TateComparison.Add.Tate.Module (H := Additive (Over.mk b ⟶ A.scheme)) q) := by
  have := geometricTorsion_finite_from_TorsionQuotient base A k b q 1
  exact TateComparison.FiniteGeneration.Tate.finite_of_finite_torsion q
    (TateKernel.Construction.geometricPoint_q_divisible_from_TorsionQuotient base A b q Fact.out Torsion.Construction.verified_TorsionQuotientInput)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateFiniteness.Construction
