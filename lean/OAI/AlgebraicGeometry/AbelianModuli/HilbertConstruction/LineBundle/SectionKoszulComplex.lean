import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulStep
import Mathlib.Algebra.Homology.Single

/-! # Section Koszul Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulComplex

noncomputable section

/-! The actual finite section Koszul complex has a bounded range of degrees and contracts after every pullback on which one of its sections is a frame. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

local instance e33KoszulComplexTensorAdditive {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

local instance e33KoszulComplexPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

theorem lineBundleTensor_pullback_contractible {X Y : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (f : Y ⟶ X) (K : CochainComplex X.Modules ℤ)
    (hK : Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj K)) 0)) :
    Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      ((((TensorEquivalence.lineBundleTensorEquivalence L).functor).mapHomologicalComplex (.up ℤ)).obj K))) 0) := by
  let P := Scheme.Modules.pullback f
  let T := (TensorEquivalence.lineBundleTensorEquivalence L).functor
  let T' := (TensorEquivalence.lineBundleTensorEquivalence (L.pullback f)).functor
  change Nonempty (Homotopy (𝟙 (((T ⋙ P).mapHomologicalComplex (.up ℤ)).obj K)) 0)
  let e : T ⋙ P ≅ P ⋙ T' := TensorPullbackFunctor.lineBundleTensorPullbackFunctorIso f L
  let eK := (NatIso.mapHomologicalComplex e (.up ℤ)).app K
  exact MappingConeContractions.cochainContractible_of_iso eK
    (MappingConeContractions.cochainContractible_map T' ((P.mapHomologicalComplex (.up ℤ)).obj K) hK)

theorem lineBundleSectionKoszulStep_pullback_contractible_of_tail
    {X Y : Scheme.{u}} (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    (f : Y ⟶ X) (K : CochainComplex X.Modules ℤ)
    (hK : Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj K)) 0)) :
    Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      (SectionKoszulStep.lineBundleSectionKoszulStep L s K))) 0) := by
  let P := Scheme.Modules.pullback f
  change Nonempty (Homotopy (𝟙 ((P.mapHomologicalComplex (.up ℤ)).obj
    (CochainComplex.mappingCone (SectionKoszulStep.lineBundleSectionComplexMap L s K)))) 0)
  let q := (P.mapHomologicalComplex (.up ℤ)).map (SectionKoszulStep.lineBundleSectionComplexMap L s K)
  let e : (P.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mappingCone (SectionKoszulStep.lineBundleSectionComplexMap L s K)) ≅ CochainComplex.mappingCone q :=
    CochainComplex.mappingCone.mapHomologicalComplexIso (SectionKoszulStep.lineBundleSectionComplexMap L s K) P
  exact MappingConeContractions.cochainContractible_of_iso e (MappingConeContractions.mappingCone_contractible_of_contractible q hK
    (lineBundleTensor_pullback_contractible L f K hK))

def lineBundleSectionKoszulComplex {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (M : X.Modules) :
    List (Line.Bundles.structureModule X ⟶ L.sheaf) → CochainComplex X.Modules ℤ
  | [] => (HomologicalComplex.single X.Modules (.up ℤ) 0).obj M
  | s :: ss => SectionKoszulStep.lineBundleSectionKoszulStep L s (lineBundleSectionKoszulComplex L M ss)

theorem lineBundleSectionKoszulComplex_pullback_contractible
    {X Y : Scheme.{u}} (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) (f : Y ⟶ X)
    (hs : ∃ s ∈ ss, IsIso ((Scheme.Modules.pullback f).map s)) :
    Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      (SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss))) 0) := by
  induction ss with
  | nil => simp at hs
  | cons s ss ih =>
    obtain ⟨t, ht, htiso⟩ := hs
    rcases List.mem_cons.mp ht with rfl | ht
    · have := htiso
      exact ⟨SectionKoszulStep.lineBundleSectionKoszulStep_pullback_contractible L t f
        (SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss)⟩
    · exact lineBundleSectionKoszulStep_pullback_contractible_of_tail L s f
        (SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss) (ih ⟨t, ht, htiso⟩)

theorem lineBundleSectionKoszulComplex_isZero_X {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (M : X.Modules) (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) (i : ℤ)
    (hi : i < -(ss.length : ℤ) ∨ 0 < i) :
    IsZero ((SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i) := by
  induction ss generalizing i with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i
      (by simp only [List.length_nil, Nat.cast_zero, neg_zero] at hi; omega)
  | cons s ss ih =>
    apply (SectionKoszulStep.lineBundleSectionKoszulStep_isZero_X_iff L s _ i).mpr
    constructor
    · apply ih
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi
      omega
    · exact Functor.map_isZero (TensorEquivalence.lineBundleTensorEquivalence L).functor
        (ih i (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulComplex
