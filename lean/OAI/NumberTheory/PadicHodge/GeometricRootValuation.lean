import OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricRootAt

/-! # Geometric Root Valuation -/

namespace OAI.NumberTheory.PadicHodge.GeometricRootValuation.CM.ExtremeSlopesAdapter.Geometric

noncomputable section

/-- Expose the canonical value through a checked equation before specializing
its closure map to a constructed native embedding. -/
theorem native_value_eq_canonical (q : ℕ) [Fact q.Prime]
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) (x : AlgebraicClosure ℚ) :
    RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι x = Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι x) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricRootValuation.CM.ExtremeSlopesAdapter.Geometric
