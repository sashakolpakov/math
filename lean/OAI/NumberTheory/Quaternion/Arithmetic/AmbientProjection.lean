import OAI.NumberTheory.Quaternion.Arithmetic.Volume
import OAI.NumberTheory.Quaternion.Arithmetic.SelectedArithmeticProduct

/-! # Ambient Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AmbientProjection

noncomputable section

/-! Reindexing the S-union-T local quotient as the actual omitted
and selected product used in the strong approximation reduction. -/

open scoped Classical
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def omittedSelectedIndex (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) (v : (S : Set (LocalAdeles.Place F))) :
    (SelectedArithmeticProduct.selectedArithmeticPlaces S T : Set (LocalAdeles.Place F)) :=
  ⟨v.val, Finset.mem_union_left _ v.property⟩

def selectedSelectedIndex (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) (v : (T : Set (ApproximationTopology.AwayPlace S))) :
    (SelectedArithmeticProduct.selectedArithmeticPlaces S T : Set (LocalAdeles.Place F)) :=
  ⟨v.val.val, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩)⟩

def selectedAmbientProjection (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) :
    Ambient.OmittedLocalProduct G (SelectedArithmeticProduct.selectedArithmeticPlaces S T) →*
      Ambient.OmittedLocalProduct G S × Groups.SelectedLocalProduct G S T where
  toFun g := (fun v => g (omittedSelectedIndex S T v), fun v => g (selectedSelectedIndex S T v))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem selectedAmbientProjection_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) : Continuous (selectedAmbientProjection G S T) :=
  (continuous_pi (fun v => continuous_apply (omittedSelectedIndex S T v))).prodMk
    (continuous_pi (fun v => continuous_apply (selectedSelectedIndex S T v)))

omit [NumberField F] in
theorem selectedPlace_mem_T_of_not_mem_S (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))
    (v : (SelectedArithmeticProduct.selectedArithmeticPlaces S T : Set (LocalAdeles.Place F))) (hv : v.val ∉ S) :
    (⟨v.val, hv⟩ : ApproximationTopology.AwayPlace S) ∈ T := by
  have ht := (Finset.mem_union.mp v.property).resolve_left hv
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp ht
  exact (Subtype.ext he : w = ⟨v.val, hv⟩) ▸ hw

theorem selectedAmbientProjection_surjective (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) : Function.Surjective (selectedAmbientProjection G S T) := by
  intro x
  let y : Ambient.OmittedLocalProduct G (SelectedArithmeticProduct.selectedArithmeticPlaces S T) := fun v =>
    if hv : v.val ∈ S then x.1 ⟨v.val, hv⟩
      else x.2 ⟨⟨v.val, hv⟩, selectedPlace_mem_T_of_not_mem_S S T v hv⟩
  refine ⟨y, Prod.ext ?_ ?_⟩
  · funext v
    exact dite_eq_left v.property
  · funext v
    exact dite_eq_right v.val.property

theorem selectedAmbientProjection_arithmetic (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S)) :
    (Adelic.sArithmeticLocalSubgroup G (SelectedArithmeticProduct.selectedArithmeticPlaces S T)).map (selectedAmbientProjection G S T) =
      Ambient.arithmeticAmbientSubgroup G S T := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨q, hq, he⟩ := (Adelic.sArithmeticLocalSubgroup_mem G (SelectedArithmeticProduct.selectedArithmeticPlaces S T) z).mp hz
    have hq' : q ∈ Groups.arithmeticSubgroup G S T := (SelectedArithmeticProduct.arithmeticSubgroup_eq_selectedIntegral G S T).ge hq
    refine ⟨⟨q, hq'⟩, Prod.ext ?_ ?_⟩
    · funext v
      exact he (omittedSelectedIndex S T v)
    · funext v
      exact he (selectedSelectedIndex S T v)
  · rintro ⟨q, rfl⟩
    let z : Ambient.OmittedLocalProduct G (SelectedArithmeticProduct.selectedArithmeticPlaces S T) := fun v => LocalAdeles.diagonalLocal G v.val q.val
    have hz : z ∈ Adelic.sArithmeticLocalSubgroup G (SelectedArithmeticProduct.selectedArithmeticPlaces S T) :=
      (Adelic.sArithmeticLocalSubgroup_mem G _ z).mpr
        ⟨q.val, (SelectedArithmeticProduct.arithmeticSubgroup_eq_selectedIntegral G S T).le q.property, fun _ => rfl⟩
    exact ⟨z, hz, rfl⟩

theorem arithmeticAmbient_quotientProbability_of_full (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S)
    [CompactSpace (AdelicGroup.FullAdelicGroupPoints G ⧸ (AdelicGroup.diagonalFullAdelic G).range)]
    (T : Finset (ApproximationTopology.AwayPlace S)) : CompactQuotientProjection.QuotientHasInvariantProbability (Ambient.arithmeticAmbientSubgroup G S T) :=
  CompactQuotientProjection.quotientProbability_of_surjective (selectedAmbientProjection G S T)
    (selectedAmbientProjection_continuous G S T) (selectedAmbientProjection_surjective G S T)
    _ _ (selectedAmbientProjection_arithmetic G S T).le
    (Volume.sArithmeticLocal_quotientProbability_of_full G (SelectedArithmeticProduct.selectedArithmeticPlaces S T)
      (fun v => Finset.mem_union_left _ (harch v)))

end

end OAI.NumberTheory.Quaternion.Arithmetic.AmbientProjection
