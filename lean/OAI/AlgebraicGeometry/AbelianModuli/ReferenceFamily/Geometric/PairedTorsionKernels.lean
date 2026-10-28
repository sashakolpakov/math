import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points

/-! # Paired Torsion Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedTorsionKernels

noncomputable section

/-! On each original geometric point, the image on n-torsion of
one isogeny is exactly the kernel on n-torsion of its scalar complement.
The required lift comes from the actual surjective scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points.Construction

theorem geometric_paired_torsion_image_kernel
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] [Surjective q.left] [LocallyOfFiniteType q.left]
    (v : B ⟶ A) [IsMonHom v] (n : ℕ) (hqv : q ≫ v = (𝟙 A) ^ n)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) :
    (IsMonHom.monoidHom (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) (Over.mk s)).range =
      (IsMonHom.monoidHom (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v) (Over.mk s)).ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply (Paired.PELKernelAnnihilator.nativeTorsionMap_kernel_point_iff v n (Over.mk s) _).mpr
    change ((x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) ≫ v = 1
    calc
      ((x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) ≫ v =
          (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) ≫ (q ≫ v) := by
        simp only [Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion]
      _ = (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) ^ n := by
        rw [hqv, MonObj.comp_pow, Category.comp_id]
      _ = 1 := by rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion_killed, MonObj.comp_one]
  · intro hy
    have hy' := (Paired.PELKernelAnnihilator.nativeTorsionMap_kernel_point_iff v n (Over.mk s) y).mp hy
    obtain ⟨a, ha⟩ := AbelianScheme.IsogenyQuotient.Geometric.Points.Construction.surjective_on_geometric_points q k s (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)
    change a ≫ q = y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n at ha
    have han : a ^ n = 1 := by
      calc
        a ^ n = a ≫ (𝟙 A) ^ n := by rw [MonObj.comp_pow, Category.comp_id]
        _ = a ≫ (q ≫ v) := by rw [hqv]
        _ = (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) ≫ v := by rw [← Category.assoc, ha]
        _ = 1 := hy'
    refine ⟨AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A n a han, ?_⟩
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)).mp
    change (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A n a han ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n = _
    rw [Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion]
    exact ha

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedTorsionKernels
