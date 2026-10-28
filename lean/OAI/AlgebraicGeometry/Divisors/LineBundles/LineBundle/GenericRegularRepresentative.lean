import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ReferenceSection

/-! # Generic Regular Representative -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: every nonzero rational line-bundle section has an actual regular unit representative near the generic point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericRationalSectionUnitNeighborhood (a : X.functionFieldˣ) :
    L.RationalSectionUnitNeighborhood a (genericPoint X) := by
  let R := RationalBoundary.BundleCycles.rationalUnitRepresentative X a.val a.ne_zero
  let U : X.Opens := R.domain ⊓ L.rationalReferenceOpen
  have hη : genericPoint X ∈ U := ⟨
    ((genericPoint_spec X).mem_open_set_iff R.domain.isOpen).mpr (by simpa using R.nonempty_domain),
    L.mem_trivializingOpen (genericPoint X)⟩
  let : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  refine ⟨U, inf_le_right, hη,
    Units.map (X.presheaf.map (homOfLE (show U ≤ R.domain from inf_le_left)).op).hom.toMonoidHom R.unit, ?_⟩
  rw [L.rationalSectionCoordinate_reference, mul_one]
  apply Units.ext
  exact (RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict (show U ≤ R.domain from inf_le_left) R.unit.val).trans R.represents

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericRationalSectionUnitNeighborhood_coefficient (a : X.functionFieldˣ) :
    L.genericSectionCoefficient (L.genericRationalSectionUnitNeighborhood a).openSet
      (L.genericRationalSectionUnitNeighborhood a).localSection = a.val :=
  (L.genericSectionCoefficient_eq_local (genericPoint X) _
    (L.genericRationalSectionUnitNeighborhood a).subordinate _).trans
      (L.genericRationalSectionUnitNeighborhood a).localSection_coefficient

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
