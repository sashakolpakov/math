import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SectionGluing
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumLayerNormalPair
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumDimensionBounds

/-! # Reference Stratification -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: a genuine positive-codimension stratification of the reference complement

The complement of the nonempty reference trivializing open is an actual closed
algebraic subset. Its finite smooth stratification has strictly smaller
function-field dimension in every piece, because no piece closure contains
the generic point. This supplies the dimension bound needed for support purity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

/-- The actual algebraic closed subset outside the rational section's reference chart. -/
def Line.Bundles.AlgebraicLineBundle.referenceComplement : Closeds X.carrier :=
  ⟨(L.rationalReferenceOpen : Set X.carrier)ᶜ, L.rationalReferenceOpen.isOpen.isClosed_compl⟩

/-- The existing Noetherian construction supplies its finite smooth algebraic stratification. -/
def Line.Bundles.AlgebraicLineBundle.referenceStratification : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification X.structureMap
    (L.referenceComplement : Set X.carrier) :=
  Classical.choice (CycleClass.Geometric.IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed X.structureMap L.referenceComplement)

/-- Any stratum of the reference complement has closure missing the generic point. -/
theorem Line.Bundles.AlgebraicLineBundle.referencePiece_dimension_lt (P : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.structureMap)
    (hP : P.support ⊆ L.referenceComplement) :
    P.dimension < Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  rw [P.dimension_eq_closure]
  let T : IrreducibleCloseds X.carrier :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.carrier, isClosed_univ⟩
  have hclosure : (P.closureSupport : Set X.carrier) ⊆ L.referenceComplement :=
    closure_minimal hP L.referenceComplement.isClosed
  have hPT : P.closureSupport < T := by
    apply lt_of_le_not_ge (Set.subset_univ _)
    intro hTP
    exact hclosure (hTP (Set.mem_univ (genericPoint X.carrier))) (L.mem_trivializingOpen _)
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt P.closureSupport T X.structureMap hPT).trans_le
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le T X.structureMap)

/-- Every piece of the actual finite filtration satisfies that strict dimension bound. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceLayer_complexDimension_lt
    (i : Fin L.referenceStratification.analyticSupportList.length) :
    (L.referenceStratification.analyticFiltrationPiece i).complexDimension <
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap := by
  rw [CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece.complexDimension_eq_dimension]
  apply L.referencePiece_dimension_lt
  exact (CycleClass.Geometric.IntegralSmoothStratification.support_subset_integralSmoothPiecesSupport
    (L.referenceStratification.analyticFiltrationPiece_mem i)).trans
    (le_of_eq L.referenceStratification.cover)

/-- The real normal codimension of each actual smooth layer is at least two. -/
theorem Line.Bundles.AlgebraicLineBundle.referenceLayer_realCodimension_ge_two
    (i : Fin L.referenceStratification.analyticSupportList.length) :
    2 ≤ 2 * (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.structureMap -
      (L.referenceStratification.analyticFiltrationPiece i).complexDimension) := by
  have h := L.referenceLayer_complexDimension_lt i
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.structureMap] at h
  omega

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
