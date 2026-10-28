import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # PEL Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction.IsogenyQuotient

noncomputable section

/-! Transport of the universal isogeny along the commuting source and target
squares. Every comparison is a PEL-family isomorphism, so it retains the
Poincaré bundle, polarization, integral action, and full ordered marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {g N n : ℕ}
  {X Y Q Q' : Scheme.{u}}
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData R g N X) (U : AbelianScheme.TateComparison.PEL.PELFamilyData R g N Y)
  (i : X ⟶ Y) (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A (U.pullback i))

def restrictionFamilyIso (r : Q' ⟶ Q) (s : Q ⟶ Y) (s' : Q' ⟶ X)
    (hs : r ≫ s = s' ≫ i) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (A.pullback s') ((U.pullback s).pullback r) :=
  (e.pullback s').trans ((U.pullbackComp i s').trans
    (U.pullbackFactor r s (s' ≫ i) hs))

def restrictPELIsogeny (r : Q' ⟶ Q) (s t : Q ⟶ Y) (s' t' : Q' ⟶ X)
    (hs : r ≫ s = s' ≫ i) (ht : r ≫ t = t' ≫ i)
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (U.pullback s) (U.pullback t) n) :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback s') (A.pullback t') n :=
  (f.pullback r).transport (restrictionFamilyIso A U i e r s s' hs)
    (restrictionFamilyIso A U i e r t t' ht).symm

theorem restrictPELIsogeny_hom (r : Q' ⟶ Q) (s t : Q ⟶ Y) (s' t' : Q' ⟶ X)
    (hs : r ≫ s = s' ≫ i) (ht : r ≫ t = t' ≫ i)
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (U.pullback s) (U.pullback t) n) :
    (restrictPELIsogeny A U i e r s t s' t' hs ht f).isogeny.hom =
      (restrictionFamilyIso A U i e r s s' hs).abelian.hom ≫
        (Over.pullback r).map f.isogeny.hom ≫
          (restrictionFamilyIso A U i e r t t' ht).abelian.inv :=
  AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PELRestriction.IsogenyQuotient
