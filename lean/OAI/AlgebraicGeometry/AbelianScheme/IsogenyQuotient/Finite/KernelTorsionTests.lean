import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

/-! # Kernel Torsion Tests -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.KernelTorsionTests.Construction

noncomputable section

/-! For a finite locally free kernel over a field, an exponent checked
on affine locally noetherian tests holds on every scheme-valued test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup.Construction

universe u
variable {k : Type u} [Field k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]

omit [IsMonHom f] in
theorem finiteKernel_torsion_of_affine_noetherian_tests (n : ℕ)
    (h : ∀ (T : Over (Spec (.of k))) [IsAffine T.left] [IsLocallyNoetherian T.left]
      (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ A) (hx : x ≫ f = 1) : x ^ n = 1 := by
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨inferInstance, inferInstance, inferInstance⟩).1
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left := isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom
  have : IsLocallyNoetherian (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom
  have hj := h (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp f)
  obtain ⟨z, hz, _⟩ := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal f T x).mp hx
  rw [← hz, ← MonObj.comp_pow, hj, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.KernelTorsionTests.Construction
