import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassMap

/-! # Open Top Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenTopClass

noncomputable section

/-! The actual pushed section restriction and principal reindex send
the full-intersection class to the class of its literal restriction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SymbolCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  (N : Y.Modules) {m : ℕ} (t : Fin m → Γ(Z,U))

abbrev source := (Principal.AdditiveSections.additiveFunctor U hU).obj
  ((Scheme.Modules.pushforward π).obj N)
abbrev target := (Principal.AdditiveSections.additiveFunctor V hV).obj N
abbrev reindex := OpenReindex.reindex π U V hVU
abbrev family := PrincipalPoint.Fraction.family U t

def coefficientMap : source π U hU N ⟶
    (reindex π U V hVU).op ⋙ target V hV N :=
  (OpenReindex.pushforwardIso π U hU N).hom ≫
    OpenReindex.restriction π U hU V hV hVU N

def complexMap : AugmentedOrdered.Cech.complex (family U t) (source π U hU N) ⟶
    AugmentedOrdered.Cech.complex
      (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
      (target V hV N) :=
  AugmentedOrdered.CechFunctor.complexMap (family U t) (coefficientMap π U hU V hV hVU N) ≫
    (AugmentedOrdered.CechReindex.iso (reindex π U V hVU) (family U t) (target V hV N)).hom

def restriction : Γ(N,π ⁻¹ᵁ Principal.SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t)) →+
    Γ(N,Principal.SectionPresheaf.openSubset V (PrincipalResidue.SymbolCoordinates.top V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))) :=
  (N.presheaf.map (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π U V hV hVU t)).op).hom

theorem coefficient :
    (coefficientMap π U hU V hV hVU N).app (op (PrincipalResidue.SymbolCoordinates.top U t)) ≫
      AugmentedOrdered.CechReindexTop.coefficient (reindex π U V hVU)
        (family U t) m (by simp) (target V hV N) =
    N.presheaf.map (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π U V hV hVU t)).op := by
  change (𝟙 _ ≫ N.presheaf.map _) ≫ N.presheaf.map _ = N.presheaf.map _
  rw [Category.id_comp, ← N.presheaf.map_comp]
  congr 1

theorem comparison :
    AugmentedCech.TopClassMap.map (family U t) (source π U hU N) m (by simp) ≫
      homologyMap (complexMap π U hU V hV hVU N t) m =
    N.presheaf.map (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π U V hV hVU t)).op ≫
      AugmentedCech.TopClassMap.map
        (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
        (target V hV N) m (by simp) := by
  rw [complexMap, homologyMap_comp, ← Category.assoc,
    AugmentedCech.TopClassMap.naturality, Category.assoc,
    AugmentedCech.TopClassMap.reindex, ← Category.assoc, coefficient]
  rfl

theorem apply (x : Γ(N,π ⁻¹ᵁ Principal.SectionPresheaf.openSubset U (PrincipalResidue.SymbolCoordinates.top U t))) :
    homologyMap (complexMap π U hU V hV hVU N t) m
      (AugmentedCech.TopClassMap.map (family U t) (source π U hU N) m (by simp) x) =
    AugmentedCech.TopClassMap.map
      (PrincipalPoint.Fraction.family V (PrincipalResidue.ResidueRestriction.parameters π U V hVU t))
      (target V hV N) m (by simp) (restriction π U V hV hVU N t x) :=
  ConcreteCategory.congr_hom (comparison π U hU V hV hVU N t) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenTopClass
