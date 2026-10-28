import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPermutation
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalExterior

/-! # Packed Permutation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedPermutation.CM.Construction

noncomputable section

theorem packH1Cup_perm_algebraic_iff
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (p : ℕ) (v : Fin (p + p) → A.variety.complexCohomology 1)
    (σ : Equiv.Perm (Fin (p + p))) :
    PackedRegroup.CM.Construction.IsAlgebraicEven A.variety (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace A.toOver) p (v ∘ σ)) ↔
      PackedRegroup.CM.Construction.IsAlgebraicEven A.variety (PackedRegroup.CM.Construction.packH1Cup (Betti.Scheme.schemePointSpace A.toOver) p v) := by
  constructor
  · intro h
    have hi := CupPermutation.CM.Construction.h1Cup_perm_mem (CanonicalExterior.CM.Construction.canonicalExterior hexterior A) p (v ∘ σ) σ.symm h
    have heq : (v ∘ σ) ∘ σ.symm = v := by funext i; simp
    rw [heq] at hi
    exact hi
  · exact CupPermutation.CM.Construction.h1Cup_perm_mem (CanonicalExterior.CM.Construction.canonicalExterior hexterior A) p v σ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedPermutation.CM.Construction
