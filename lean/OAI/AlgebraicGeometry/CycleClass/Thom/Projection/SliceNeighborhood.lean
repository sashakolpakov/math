import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations

/-! # Slice Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceNeighborhood.Constructions

noncomputable section

/-! Actual maps of pairs from an isolating slice open into a sheet's normal neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceEquations.Constructions

variable {M L N E W : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup W]
  {c d : ℕ} {f : M → N} {x : M} {i : L → N × (Fin d → ℂ)} {y : L}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair W (Fin (c + d) → ℂ) i y)
  (V : Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × (Fin d → ℂ)))
  (hV : Set.MapsTo (Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) (id : (Fin d → ℂ) → (Fin d → ℂ)))
    (V : Set _) Q.neighborhood)

def sliceToPair : TopCat.of V ⟶ TopCat.of Q.neighborhood :=
  TopCat.ofHom ⟨fun z => ⟨Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id z.val, hV z.property⟩,
    (((Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P).hom.continuous.prodMap continuous_id).comp
      continuous_subtype_val).subtype_mk _⟩

def sliceEquationMap : TopCat.of V ⟶ TopCat.of (Fin (c + d) → ℂ) :=
  sliceToPair P Q V hV ≫ Q.normalCoordinate

theorem sliceEquationMap_eq : (sliceEquationMap P Q V hV : V → (Fin (c + d) → ℂ)) =
    SliceEquations.Constructions.sliceEquations P Q ∘ Subtype.val := rfl

theorem sliceToPair_mapsTo (z : V)
    (hIso : ∀ a : V, Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id a.val ∈ Set.range i → a = z) :
    Set.MapsTo (sliceToPair P Q V hV) ({z}ᶜ) Q.relativeComplement := by
  intro a ha hi
  exact ha (hIso a hi)

theorem sliceEquationMap_mapsTo (z : V)
    (hIso : ∀ a : V, Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id a.val ∈ Set.range i → a = z) :
    Set.MapsTo (sliceEquationMap P Q V hV) ({z}ᶜ) ({0}ᶜ) :=
  Q.normalCoordinate_mapsTo.comp (sliceToPair_mapsTo P Q V hV z hIso)

theorem sliceToPair_Thom_pullback [NormedSpace ℝ W] (z : V)
    (hIso : ∀ a : V, Prod.map (Normal.SliceAnalytic.Constructions.normalSliceAmbientMap P) id a.val ∈ Set.range i → a = z) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (sliceToPair P Q V hV)
      (sliceToPair_mapsTo P Q V hV z hIso) (2 * (c + d)) Q.rationalClassFin =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (sliceEquationMap P Q V hV)
      (sliceEquationMap_mapsTo P Q V hV z hIso) (2 * (c + d))
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (c + d)) := by
  rw [Q.rationalClassFin_eq_normalPullback]
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (sliceToPair P Q V hV) Q.normalCoordinate
      (sliceToPair_mapsTo P Q V hV z hIso) Q.normalCoordinate_mapsTo (2 * (c + d)))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (c + d))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Projection.SliceNeighborhood.Constructions
