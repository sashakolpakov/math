import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalPullback

/-! # Generic Fiber Divisor Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: a pulled-back rational divisor vanishes over the generic point
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def RationalBoundary.BundleCycles.RationalUnitRepresentative.pullbackGeneric {g : Y.functionField}
    (D : RationalBoundary.BundleCycles.RationalUnitRepresentative Y g) (f : X ⟶ Y)
    (hη : f (genericPoint X) = genericPoint Y) :
    RationalBoundary.BundleCycles.RationalUnitRepresentative X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) := by
  have hmem : genericPoint Y ∈ D.domain :=
    ((genericPoint_spec Y).mem_open_set_iff D.domain.isOpen).mpr
      (by simpa using D.nonempty_domain)
  have hn : Nonempty (f ⁻¹ᵁ D.domain) := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ D.domain
    rw [hη]
    exact hmem⟩⟩
  refine { domain := f ⁻¹ᵁ D.domain
           nonempty_domain := hn
           unit := Units.map (f.app D.domain).hom.toMonoidHom D.unit
           represents := ?_ }
  have h := ConcreteCategory.congr_hom (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn f hη D.domain)
    (D.unit : Γ(Y, D.domain))
  exact h.symm.trans (congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) D.represents)

theorem GenericFiberDivisorZero.BundleCycles.ord_pullback_zero_over_generic [IsLocallyNoetherian X]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (g : Y.functionField) (hg : g ≠ 0) (x : X) (hx : f x = genericPoint Y) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) x = 0 := by
  let D := RationalBoundary.BundleCycles.rationalUnitRepresentative Y g hg
  apply (D.pullbackGeneric f hη).ord_eq_zero x
  change f x ∈ D.domain
  rw [hx]
  exact ((genericPoint_spec Y).mem_open_set_iff D.domain.isOpen).mpr
    (by simpa using D.nonempty_domain)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
