import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.FactorShiftUnramified
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusShiftEtale

/-! # Frobenius Factor Shift Etale -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusFactorShiftEtale

noncomputable section

/-! Actual finite étale geometric shifts of every original endomorphism
factoring through Frobenius. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

universe u
variable (k : Type u) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

theorem geometric_shift_eq (r : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom.left =
      AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberMap k ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom := by
  have h : AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) =
      (n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) := by
    rw [map_sub, map_natCast]
  exact (congrArg (fun z : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A) => z.toMul.hom.hom.left) h).symm

theorem formallyUnramified (r : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) (hn : (n : k) ≠ 0) :
    FormallyUnramified ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom.left := by
  rw [geometric_shift_eq]
  exact MorphismProperty.of_isPullback (P := @FormallyUnramified)
    (AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapBaseChange.Construction.geometricFiberMap_isPullback k
      ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A).toMul.hom.hom).flip
    (Frobenius.FactorShiftUnramified.formallyUnramified k A r n hn)

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem finite_etale (r : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) (hn : (n : k) ≠ 0) :
    IsFinite ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom.left ∧
    Surjective ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom.left ∧
    Etale ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom.left := by
  let T := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A
  let : IsProper T.hom := inferInstanceAs (IsProper (pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k)))
  let : Smooth T.hom := inferInstanceAs (Smooth (pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k)))
  let : GeometricallyIntegral T.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase k)))
  let g := ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd T) -
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (r * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)).toMul.hom.hom
  let : FormallyUnramified g.left := formallyUnramified k A r n hn
  let : IsProper (g.left ≫ T.hom) := by rw [Over.w]; infer_instance
  let : IsProper g.left := IsProper.of_comp g.left T.hom
  let : IsFinite g.left := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified g.left
  let : IsIntegral T.left := GeometricallyIntegral.isIntegral_of_subsingleton T.hom
  let : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  let : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  let : IsNoetherian T.left := ⟨⟩
  let : Surjective g.left := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteEndomorphism.Construction.surjective_finite_endomorphism_of_isIntegral g.left
  let : Flat g.left := AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat g
  let : LocallyOfFinitePresentation (g.left ≫ T.hom) := by rw [Over.w]; infer_instance
  let : LocallyOfFinitePresentation g.left := AlgebraicGeometry.AbelianScheme.TorsionQuotient.FinitePresentationOf.FinitePresentation.of_comp g.left T.hom
  exact ⟨inferInstance, inferInstance, Etale.of_formallyUnramified_of_flat g.left⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusFactorShiftEtale
