import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalUnitNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MovedSectionNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.LocalUnitTrivialization

/-! # Rational Section Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: actual unit-valued neighborhood representatives of a rational line-bundle section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X]

/-- A regular unit in an actual local frame representing the specified rational section.
The data contains only an open neighborhood, a regular unit, and its generic coefficient. -/
structure Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a : X.functionFieldˣ) (x : X) where
  openSet : X.Opens
  subordinate : openSet ≤ L.trivializingOpen x
  point_mem : x ∈ openSet
  unit : Γ(X, openSet)ˣ
  generic_eq : letI : Nonempty openSet := ⟨⟨x, point_mem⟩⟩
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm openSet unit = a * L.rationalSectionCoordinate x

variable (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a : X.functionFieldˣ) (x : X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionUnitNeighborhood_nonempty [AlgebraicGeometry.IsNoetherian X]
    (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0) :
    Nonempty (L.RationalSectionUnitNeighborhood a x) := by
  obtain ⟨U, hU, hxU, u, hu⟩ := L.exists_rationalSection_unit_neighborhood a x hx ha
  exact ⟨⟨U, hU, hxU, u, hu⟩⟩

variable {L a x} (D : L.RationalSectionUnitNeighborhood a x)

instance Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.openSet_nonempty : Nonempty D.openSet := ⟨⟨x, D.point_mem⟩⟩

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.localSection : Γ(L.sheaf, D.openSet) := L.rationalUnitLocalSection x D.openSet D.subordinate D.unit

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.localSection_coordinate : L.sectionFrame x D.openSet D.subordinate D.localSection = D.unit.val :=
  L.rationalUnitLocalSection_coordinate x D.openSet D.subordinate D.unit

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.localSection_coefficient : L.localRationalCoefficient x D.openSet D.subordinate D.localSection = a.val :=
  L.rationalUnitLocalSection_coefficient a x D.openSet D.subordinate D.unit D.generic_eq

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.trivialization : L.sheaf.restrict D.openSet.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule D.openSet.toScheme :=
  L.localUnitSectionTrivialization x D.openSet D.subordinate D.localSection
    (D.localSection_coordinate.symm ▸ D.unit.isUnit)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.trivialization_generator :
    LineBundle.GlobalFrame.Cycles.lineBundleGlobalFrame (L := L.restrictToOpen D.openSet.ι) D.trivialization ⊤
      (Module.SectionHom.BundleCycles.moduleSectionAsGlobal L.sheaf D.openSet D.localSection) = 1 :=
  L.localUnitSectionTrivialization_generator x D.openSet D.subordinate D.localSection
    (D.localSection_coordinate.symm ▸ D.unit.isUnit)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
