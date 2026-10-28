import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRingEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberBundleIsomorphisms

/-! # Fiber End Ring -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A rational fiber identifies the endomorphism rings of a line bundle on a connected reduced proper scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

def Line.Bundles.LineBundle.rationalFiberEndRingEquiv (p : X ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) (L : Line.Bundles.LineBundle X) :
    End L.sheaf ≃+* End (L.pullback x).sheaf := by
  letI : IsIso x.appTop := (Proper.ConnectedReducedConstants.properConnectedReducedPointGlobalIso p x hx).isIso_inv
  refine RingEquiv.ofBijective (LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pullback x) L.sheaf)
    ⟨Line.Bundles.LineBundle.endPullback_atRationalPoint_injective p x hx L (L.pullback x).trivialization_of_subsingleton.symm,
      ?_⟩
  intro ψ
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso x.appTop).2 ((L.pullback x).endScalar ψ)
  refine ⟨Global.ModuleScalars.globalModuleScalar L.sheaf r, ?_⟩
  change (Scheme.Modules.pullback x).map (Global.ModuleScalars.globalModuleScalar L.sheaf r) = ψ
  rw [Global.ScalarBaseChange.globalModuleScalar_pullback, hr]
  apply (L.pullback x).endScalar_injective
  exact (L.pullback x).endScalar_globalModuleScalar ((L.pullback x).endScalar ψ)

theorem Line.Bundles.LineBundle.rationalFiberEndRingEquiv_apply (p : X ⟶ Spec (.of K))
    [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) :
    Line.Bundles.LineBundle.rationalFiberEndRingEquiv p x hx L φ = (Scheme.Modules.pullback x).map φ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
