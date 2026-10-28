import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels

/-! # Open Surjectivity Spread -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.OpenSurjectivitySpread.Abelian

noncomputable section

/-! An open map into a proper coefficient family that covers the ambient
field fiber becomes surjective after a finite coefficient enlargement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels.Coefficients

theorem open_map_to_proper_family_eventually_surjective
    {R K : Type} [CommRing R] [Field K] [Algebra R K] {s : Finset K}
    {V M : Over (Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)} [IsProper M.hom]
    (v : V ⟶ M) (hv : IsOpenMap v.left)
    (hgeneric : Surjective ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map v).left) :
    ∃ (t : Finset K) (h : s ⊆ t),
      Surjective ((Over.pullback (Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)).map v).left := by
  have hopen : IsOpen (AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus.surjectiveParameterSet v) :=
    (M.hom.isClosedMap _ hv.isOpen_range.isClosed_compl).isOpen_compl
  have hp : Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s (IsLocalRing.closedPoint K) ∈ AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus.surjectiveParameterSet v :=
    (AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus.surjective_base_change_iff_range v _).mp hgeneric (Set.mem_range_self _)
  obtain ⟨_, ⟨a, rfl⟩, ha, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hopen
  have ha0 : a ≠ 0 := by
    intro hz
    exact ha (hz ▸ (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s (IsLocalRing.closedPoint K)).asIdeal.zero_mem)
  obtain ⟨t, h, ht⟩ := AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels.Coefficients.coefficient_base_in_basicOpen a ha0
  exact ⟨t, h, (AlgebraicGeometry.PELModuli.IntegralModel.SurjectiveLocus.surjective_base_change_iff_range v _).mpr (ht.trans hsub)⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.OpenSurjectivitySpread.Abelian
