import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionFractionRestriction

/-! # Selected Symbol Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSymbolRestriction

noncomputable section

/-! A selected numerator evaluating to one disappears from the actual
restricted principal top class, with its scalar coefficient unchanged. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  (N : Y.Modules) (ω : Γ(N,π ⁻¹ᵁ U)) {m : ℕ} (t : Fin m → Γ(Z,U))
  (R : Type u) [CommRing R] [Algebra R Γ(Z,U)]

def sourceClass (a : R) :=
  AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U t)
    (PrincipalSource.OpenTopClass.source π U hU N) m (by simp)
    (PrincipalResidue.SymbolCoordinates.symbolValue π U hU t R N ω a)

variable {k : Type u} [CommRing k] (η : Γ(Y,V) →+* k)
  (hk : Koszul.OrientedTopCohomology.ideal Γ(Y,V)
    (PrincipalResidue.ResidueRestriction.parameters π U V hVU t) = RingHom.ker η)
  (z : Γ(Y,π ⁻¹ᵁ U)) (hz : η (Y.presheaf.map (homOfLE hVU).op z) = 1)

include hk hz in
theorem restriction (a : R) :
    homologyMap (PrincipalSource.OpenTopClass.complexMap π U hU V hV hVU N t) m
      (sourceClass π U hU N (z • ω) t R a) =
    homologyMap (PrincipalSource.OpenTopClass.complexMap π U hU V hV hVU N t) m
      (sourceClass π U hU N ω t R a) := by
  have hω : SectionFractionRestriction.localSection π U V hVU N (z • ω) =
      Y.presheaf.map (homOfLE hVU).op z •
        SectionFractionRestriction.localSection π U V hVU N ω := by
    dsimp only [SectionFractionRestriction.localSection]
    rw [N.map_smul]
  have hw := SectionFractionRestriction.weighted π U hU V hV hVU N
    (z • ω) t η hk (Y.presheaf.map (homOfLE hVU).op z) hz
    (SectionFractionRestriction.localSection π U V hVU N ω) hω
    (algebraMap R Γ(Z,U) a)
  have hu := SectionFractionRestriction.comparison π U hU V hV hVU N ω t
    (algebraMap R Γ(Z,U) a)
  simpa only [sourceClass, PrincipalResidue.SymbolCoordinates.symbolValue,
    PrincipalResidue.SymbolCoordinates.coefficient, Algebra.algebraMap_self, RingHom.id_apply]
    using hw.trans hu.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSymbolRestriction
