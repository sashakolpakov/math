import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalSectionNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalCoordinate

/-! # Reference Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the actual reference generator is a unit neighborhood representative of coefficient one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.referenceUnitNeighborhood : L.RationalSectionUnitNeighborhood 1 (genericPoint X) where
  openSet := L.rationalReferenceOpen
  subordinate := le_rfl
  point_mem := L.mem_trivializingOpen (genericPoint X)
  unit := 1
  generic_eq := by rw [map_one, L.rationalSectionCoordinate_reference, mul_one]

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.referenceSection : Γ(L.sheaf, L.rationalReferenceOpen) := L.referenceUnitNeighborhood.localSection

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.referenceSection_coordinate : L.sectionFrame (genericPoint X) L.rationalReferenceOpen le_rfl L.referenceSection = 1 :=
  L.referenceUnitNeighborhood.localSection_coordinate

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.referenceSection_genericCoefficient : L.genericSectionCoefficient L.rationalReferenceOpen L.referenceSection = 1 :=
  (L.genericSectionCoefficient_eq_local (genericPoint X) L.rationalReferenceOpen le_rfl L.referenceSection).trans
    L.referenceUnitNeighborhood.localSection_coefficient

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.referenceSection_restrict_coordinate (U : X.Opens) (hU : U ≤ L.rationalReferenceOpen) :
    L.sectionFrame (genericPoint X) U hU
      (L.sheaf.presheaf.map (homOfLE hU).op L.referenceSection) = 1 := by
  rw [L.sectionFrame_naturality (genericPoint X) hU le_rfl,
    L.referenceSection_coordinate, map_one]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.section_eq_reference_smul (U : X.Opens) (hU : U ≤ L.rationalReferenceOpen) (s : Γ(L.sheaf, U)) :
    s = L.sectionFrame (genericPoint X) U hU s •
      L.sheaf.presheaf.map (homOfLE hU).op L.referenceSection := by
  apply (L.sectionFrame (genericPoint X) U hU).injective
  rw [(L.sectionFrame (genericPoint X) U hU).map_smul, L.referenceSection_restrict_coordinate U hU]
  exact (mul_one _).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
