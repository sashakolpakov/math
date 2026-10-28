import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeContractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

/-! # Complex Local Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ComplexLocalExactness

noncomputable section

/-! Zero modules and exact complexes are detected on actual open restrictions. Local contracting homotopies therefore imply global exactness. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

theorem module_zero_of_restricted_zero {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i) (M : X.Modules)
    (hM : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (U i).ι).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply MapCoverEquality.moduleMap_eq_of_restrict_cover U hU
  intro i
  exact (hM i).eq_of_src _ _

theorem cochain_acyclic_of_contractible {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (hK : Nonempty (Homotopy (𝟙 K) 0)) : K.Acyclic := by
  obtain ⟨h⟩ := hK
  intro i
  apply (K.exactAt_iff_isZero_homology i).mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero]
    using h.homologyMap_eq i

local instance e33LocalExactnessPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

theorem moduleComplex_acyclic_of_pullback_contractible_cover {X : Scheme.{u}} {ι : Type v}
    (K : CochainComplex X.Modules ℤ) (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hK : ∀ i, Nonempty (Homotopy
      (𝟙 (((Scheme.Modules.pullback (U i).ι).mapHomologicalComplex (.up ℤ)).obj K)) 0)) :
    K.Acyclic := by
  intro n
  apply (K.exactAt_iff_isZero_homology n).mpr
  apply module_zero_of_restricted_zero U hU (K.homology n)
  intro i
  let R := Scheme.Modules.restrictFunctor (U i).ι
  let : PreservesLimits R := RestrictionLimits.moduleRestrictFunctor_preservesLimits (U i).ι
  let : PreservesColimits R :=
    preservesColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let e := (NatIso.mapHomologicalComplex
    (Scheme.Modules.restrictFunctorIsoPullback (U i).ι) (.up ℤ)).app K
  have hR := MappingConeContractions.cochainContractible_of_iso e (hK i)
  have hzero := (((R.mapHomologicalComplex (.up ℤ)).obj K).exactAt_iff_isZero_homology n).mp
    (cochain_acyclic_of_contractible _ hR n)
  exact ((K.sc n).mapHomologyIso R).isZero_iff.mp hzero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ComplexLocalExactness
