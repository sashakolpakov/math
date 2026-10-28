import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledOrdinaryFiber
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarizations

/-! # Theorem -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.Theorem

noncomputable section

/-! Homomorphisms for the original geometric abelian-scheme hypotheses. The base
may be nonreduced and disconnected, and relative dimension may vary.
Ordinarity is used only on each geometric fiber for the kernel equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

theorem relativeFrobenius_quotient_kernel_polarization
    (p : ℕ) [Fact p.Prime]
    (S : Over (Spec (CommRingCat.of (ZMod p))))
    (A : AbelianSchemes.Construction.AbelianScheme S.left) (ell : Polarizations.Construction.Polarization A) :
    let hS := Frobenius.Construction.prime_eq_zero_of_overFp p S.left S.hom
    let F := Frobenius.Construction.relativeFrobenius p Fact.out hS A.toOver
    Quotient.Construction.FiniteLocallyFreeHom F.left ∧ Surjective F.left ∧ Quotient.Construction.IsFppfQuotientByKernel F ∧
      (∀ s : GeometricPoints.Construction.GeometricPoint S.left,
        UnbundledOrdinaryFiber.Construction.IsOrdinary p (A.geometricFiber s).toOver →
          Subobject.mk ((Over.pullback s.map).map (Kernel.Construction.kernelInclusion F)) =
            MultiplicativeSubgroup.Construction.multiplicativePTorsion p s.field (A.geometricFiber s).toOver) ∧
      Polarizations.Construction.pullbackPolarizationHom p Fact.out hS ell = p • ell.hom := by
  let hS := Frobenius.Construction.prime_eq_zero_of_overFp p S.left S.hom
  have hF := Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A.toOver
  refine ⟨hF.1, hF.2.1, hF.2.2, ?_, Polarizations.Construction.frobenius_pullback_polarization p Fact.out hS ell⟩
  intro s hordinary
  let f : A.toOver ⟶ ell.dual.abelian := ell.map
  have : IsMonHom f := ell.preservesGroup
  have : IsFinite f.left := ell.finite
  have : Surjective f.left := ell.surjective
  exact UnbundledOrdinaryFiber.Construction.UnbundledPicard.ordinary_geometricFiber_kernel_eq_multiplicativePTorsion
    p hS A.toOver ell.dual f s.map hordinary

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.Theorem
