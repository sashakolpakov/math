import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Iso

/-! # Iso Opens -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.IsoOpens

noncomputable section

/-! The principal diagrams related by the actual frame isomorphism have
equal special-fiber open subsets, including every intersection. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))
  {P Q : AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X}

theorem opens_le (f : P ⟶ Q) : P.immersion.opensRange ≤ Q.immersion.opensRange := by
  change Set.range P.immersion ⊆ Set.range Q.immersion
  rintro x ⟨z, rfl⟩
  refine ⟨(Spec.map (CommRingCat.ofHom f.reducedMap.toRingHom)) z, ?_⟩
  exact congrArg (fun h : Spec P.residueRing ⟶ X.left => h z) f.over_X

theorem opens_eq (e : P ≅ Q) : P.immersion.opensRange = Q.immersion.opensRange :=
  le_antisymm (opens_le p k X e.hom) (opens_le p k X e.inv)

theorem principal_opens_eq (e : P ≅ Q)
    (r : AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring) :
    ((Iso.diagram p k X e).obj r).immersion.opensRange =
      (AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q r).immersion.opensRange :=
  opens_eq p k X (Iso.componentIso p k X e r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.IsoOpens
