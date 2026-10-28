import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareLineObject
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PoincareSecondZero
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardOrigin

/-! # Poincare Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareDualData.DirectedPolarizedSchemeGluing

noncomputable section

/-! The effectively glued Poincare line represents the original
homogeneous Picard sheaf on all tests. Both original zero normalizations
are retained, so this constructs actual DualAbelianData. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (C : S.OpenCover.{0})
  [Category C.I₀] [C.LocallyDirected] [Small.{0} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
local notation "E" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian C F hN e
local notation "J" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLine C F hN e
local notation "hJ" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLine_homogeneous C F hN e

omit [IsLocallyNoetherian S] in
private theorem parameterInclusion_total (i : C.I₀) :
    (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i).left =
      ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (C.f i) (F i).dual.abelian.scheme (E).scheme
        (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i) :=
  ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualData C F hN e).chartIso_fst i).symm

theorem poincare_parameter_bijective_on_chart (i : C.I₀) (T : Over (C.X i)) :
    Function.Bijective (fun a : (Over.map (C.f i)).obj T ⟶ (E).scheme =>
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ a) :=
  ReferenceFamily.DescendedPicardCoverBijection.descendedPicard_parameter_bijective_over_cover (F i).dual A (C.f i)
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) (E).scheme (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i)
    (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i) (parameterInclusion_total C F hN e i)
    J hJ (PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLine_recovery_class C F hN e i) T

theorem poincare_parameterMap_isIso : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A J hJ) := by
  let K := Scheme.fppfTopology.over S
  let a : K.uliftYoneda.{1}.obj (E).scheme ⟶ (A).homogeneousPicardSheaf :=
    ⟨RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A J hJ⟩
  have : IsIso a := by
    apply SheafOpenCoverDetection.fppfSheaf_isIso_of_baseOpenCover C a
    intro i T
    have hb := poincare_parameter_bijective_on_chart C F hN e i T
    constructor
    · intro x y hxy
      apply ULift.ext
      exact hb.injective hxy
    · intro x
      obtain ⟨b, hb⟩ := hb.surjective x
      exact ⟨ULift.up b, hb⟩
  exact inferInstanceAs (IsIso ((sheafToPresheaf K (Type 1)).map a))

/-- The original Picard sheaf is represented by the actual glued dual
scheme, via the line object just constructed. -/
def poincareRepresentable : (A).homogeneousPicardSheaf.obj.RepresentableBy (E).scheme := by
  letI := poincare_parameterMap_isIso C F hN e
  exact (Functor.RepresentableBy.equivUliftYonedaIso (A).homogeneousPicardSheaf.obj (E).scheme).symm
    (asIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A J hJ))

theorem poincareRepresentable_class (T : Over S) (a : T ⟶ (E).scheme) :
    (poincareRepresentable C F hN e).homEquiv a = RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ a := rfl

theorem poincare_parameter_origin (T : Over S) :
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ (1 : T ⟶ (E).scheme) = (A).trivialHomogeneousPicardClass T := by
  apply SheafOpenCoverDetection.fppfSheaf_eq_of_baseOpenCover (A).homogeneousPicardSheaf C T
  intro i
  let U := (Over.pullback (C.f i)).obj T
  let p := SubterminalRelativeChart.baseChartProjection (C.f i) T
  have hlocal := ReferenceFamily.DescendedPicardOrigin.descendedPicard_parameter_origin_over_cover (F i).dual A (C.f i)
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) E (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i)
    (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i) (parameterInclusion_total C F hN e i)
    J hJ (PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLine_recovery_class C F hN e i) U
  have hz : (A).homogeneousPicardSheaf.obj.map p.op ((A).trivialHomogeneousPicardClass T) =
      (A).trivialHomogeneousPicardClass ((Over.map (C.f i)).obj U) := by
    rw [(A).trivialHomogeneousPicardClass_eq_one, (A).trivialHomogeneousPicardClass_eq_one]
    exact ((A).homogeneousPicardSectionRestriction p).map_one
  exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality A J hJ (1 : T ⟶ (E).scheme) p).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ) (MonObj.comp_one p)).trans
      (hlocal.trans hz.symm))

theorem poincareRepresentable_universalClass :
    (poincareRepresentable C F hN e).homEquiv (𝟙 (E).scheme) =
      (toSheafify (Scheme.fppfTopology.over S) (A).homogeneousPicardPresheaf).app (.op (E).scheme)
        ⟨Line.Bundles.LineBundle.classOf J, hJ⟩ :=
  (poincareRepresentable_class C F hN e (E).scheme (𝟙 (E).scheme)).trans
    (ReferenceFamily.HomogeneousParameterRecovery.homogeneousParameterClass_identity A (E).scheme J hJ)

def poincareLineDualZero :
    ((J).pullback (lift (1 : (A).scheme ⟶ (E).scheme) (𝟙 (A).scheme)).left).sheaf ≅
      Line.Bundles.structureModule (A).scheme.left :=
  Classical.choice (Normalized.PoincareSecondZero.normalizedPoincare_dualZero_of_origin A (E).scheme J hJ
    (PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLineZero C F hN e) (poincare_parameter_origin C F hN e (𝟙_ (Over S))))

/-- The original dual-data structure, with an actual globally glued
Poincare line, all-test representability, and both zero rigidifications. -/
def poincareDual : Dual.Data.DualAbelianData A where
  abelian := E
  representable := poincareRepresentable C F hN e
  origin T := (poincareRepresentable_class C F hN e T 1).trans (poincare_parameter_origin C F hN e T)
  poincare := J
  poincareHomogeneous := hJ
  universalClass := poincareRepresentable_universalClass C F hN e
  normalizedAtAbelianZero := ⟨PoincareLineObject.DirectedPolarizedSchemeGluing.poincareLineZero C F hN e⟩
  normalizedAtDualZero := ⟨poincareLineDualZero C F hN e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareDualData.DirectedPolarizedSchemeGluing
