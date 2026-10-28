import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTo
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality

/-! # Pro Etale Linear -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleLinear.ProEtaleFrobeniusCohomology

noncomputable section

/-! Absolute Frobenius acts as the identity on the original integral pro-étale cohomology and its algebraic coefficient extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality.Construction OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTo.ProEtaleFrobeniusSheaves

universe u
variable (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0)

theorem integral_pullback (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (x : X.EllAdicCohomology ℓ n) :
    AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.integralEllAdicPullback ℓ (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) n x = x := by
  have hc : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (ProEtaleTo.ProEtaleFrobeniusSheaves.pullbackIso p hp X hX).app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) :=
    Iso.ext (ProEtaleTo.ProEtaleFrobeniusSheaves.constant_pullback p hp X hX (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  have hi := congrArg Iso.inv hc
  change (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).inv.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (ProEtaleTo.ProEtaleFrobeniusSheaves.pullbackIso p hp X hX).inv.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X) at hi
  change (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).H n at x
  erw [AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullback_apply, hi, ProEtaleTo.ProEtaleFrobeniusSheaves.coefficient_pullback,
    AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction.ext_mapExactFunctor_iso (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX))
      (ProEtaleTo.ProEtaleFrobeniusSheaves.pullbackIso p hp X hX), AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction.ext_mapExactFunctor_id]

theorem integral_pullback_linear (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) n = LinearMap.id := by
  ext x
  exact integral_pullback p hp X hX ℓ n x

theorem algebraic_pullback (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) = LinearMap.id := by
  unfold AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.algebraicEllAdicH1Pullback
  rw [integral_pullback_linear]
  exact LinearMap.baseChange_id

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleLinear.ProEtaleFrobeniusCohomology
