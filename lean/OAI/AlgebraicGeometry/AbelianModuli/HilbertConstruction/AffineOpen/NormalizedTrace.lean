import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingHomNormalizedTrace
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictionRingPushout
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Normalized Trace -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.NormalizedTrace

noncomputable section

/-! Normalized trace on sections of inverse-image affine opens is linear and respects restriction. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

def affineOpenNormalizedTrace (U : X.Opens) (u : Γ(X, U)ˣ) :
    Γ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule Y), U) →ₗ[Γ(X, U)] Γ(X, U) := by
  letI : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  exact Normalized.AlgebraTrace.normalizedAlgebraTrace (A := Γ(Y, f ⁻¹ᵁ U)) u

theorem affineOpenNormalizedTrace_restrict {U V : X.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hYU : IsAffineOpen (f ⁻¹ᵁ U))
    {ι : Type*} [Fintype ι]
    (b : @Module.Basis ι Γ(X, U) Γ(Y, f ⁻¹ᵁ U) _ _ (f.app U).hom.toModule)
    (u : Γ(X, U)ˣ) (a : Γ(Y, f ⁻¹ᵁ U)) :
    affineOpenNormalizedTrace f V (Units.map (X.presheaf.map (homOfLE h).op).hom u)
      (Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op a) =
      X.presheaf.map (homOfLE h).op (affineOpenNormalizedTrace f U u a) := by
  exact RingHomNormalizedTrace.ringHomNormalizedTrace_pushout (f.app U).hom
    (X.presheaf.map (homOfLE h).op).hom
    (Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op).hom
    (f.app V).hom (Affine.RestrictionRingPushout.affineRestriction_isPushout f h hU hV hYU).flip b u a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.NormalizedTrace
