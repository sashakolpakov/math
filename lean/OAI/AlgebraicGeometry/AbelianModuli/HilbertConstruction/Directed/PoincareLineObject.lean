import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareCechData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedLineObjectDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.LineOpenLocality

/-! # Poincare Line Object -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareLineObject.DirectedPolarizedSchemeGluing

noncomputable section

/-! The actual global Poincare line on the two already glued abelian
schemes. It is homogeneous, zero-normalized in the abelian factor, and
recovers each original chart Poincare line through its native map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (C : S.OpenCover.{0})
  [Category C.I₀] [C.LocallyDirected] [Small.{0} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
local notation "E" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.scheme (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian C F hN e)
local notation "V" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareCechData.DirectedPolarizedSchemeGluing.poincareCover C F hN e
local notation "D" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareCechData.DirectedPolarizedSchemeGluing.poincareLineData C F hN e

/-- This is an actual locally free rank-one sheaf, produced by native
open-cover object descent and global zero normalization. -/
def poincareLine : Line.Bundles.LineBundle (E ⊗ (A).scheme).left := (D).normalizedLineObject

def poincareLineZero :
    ((poincareLine C F hN e).pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A E).left).sheaf ≅ Line.Bundles.structureModule (E).left :=
  (D).normalizedLineObject_zero

theorem poincareLine_homogeneous :
    (A).IsHomogeneousPicardClass E (Line.Bundles.LineBundle.classOf (poincareLine C F hN e)) := by
  apply Homogeneous.LineOpenLocality.homogeneous_of_parameter_openCover A (poincareLine C F hN e) V
  intro i
  have hi : (A).IsHomogeneousPicardClass (Embedded.FamilyOpenCover.overOpenCoverObject E V i)
      (Line.Bundles.LineBundle.classOf ((D).line i).lineBundle) :=
    (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincare_homogeneous C F hN e i).pullback A (PoincareCechData.DirectedPolarizedSchemeGluing.poincareCoverParameterIso C F hN e i).hom
  exact (congrArg ((A).IsHomogeneousPicardClass (Embedded.FamilyOpenCover.overOpenCoverObject E V i))
    ((D).normalizedLineObject_recovery_class i)).mpr hi

omit [IsLocallyNoetherian S] in
theorem poincareCoverParameterIso_inclusion (i : C.I₀) :
    (PoincareCechData.DirectedPolarizedSchemeGluing.poincareCoverParameterIso C F hN e i).hom ≫ PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i =
      Embedded.FamilyOpenCover.overOpenCoverMap E V i := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

/-- Recovery with the original chart dual as parameter, without the
auxiliary cover-object structure map. -/
theorem poincareLine_recovery_class (i : C.I₀) :
    Line.Bundles.LineBundle.pullbackClass (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i ▷ (A).scheme).left
      (Line.Bundles.LineBundle.classOf (poincareLine C F hN e)) =
      Line.Bundles.LineBundle.classOf (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincare C F hN e i) := by
  let b := PoincareCechData.DirectedPolarizedSchemeGluing.poincareCoverParameterIso C F hN e i
  let q := PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i
  let c := (Over.forget S).mapIso (whiskerRightIso b (A).scheme)
  have h : c.hom ≫ (q ▷ (A).scheme).left = (Embedded.FamilyOpenCover.overOpenCoverMap E V i ▷ (A).scheme).left :=
    congrArg Over.Hom.left ((comp_whiskerRight b.hom q (A).scheme).symm.trans
      (congrArg (fun f => f ▷ (A).scheme) (poincareCoverParameterIso_inclusion C F hN e i)))
  apply (Line.Bundles.LineBundle.pullbackIso c).injective
  change Line.Bundles.LineBundle.pullbackClass c.hom
      (Line.Bundles.LineBundle.pullbackClass (q ▷ (A).scheme).left (Line.Bundles.LineBundle.classOf (poincareLine C F hN e))) =
    Line.Bundles.LineBundle.pullbackClass c.hom (Line.Bundles.LineBundle.classOf (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincare C F hN e i))
  exact (Line.Bundles.LineBundle.pullbackClass_comp c.hom (q ▷ (A).scheme).left _).symm.trans
    ((congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf (poincareLine C F hN e))) h).trans
      ((D).normalizedLineObject_recovery_class i))

def poincareLineOriginalMap (i : C.I₀) :
    ((F i).dual.abelian.scheme ⊗ (F i).abelian.scheme).left ⟶ (E ⊗ (A).scheme).left :=
  (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincareComparison C F hN e i).hom ≫
    (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i ▷ (A).scheme).left

/-- The original local Poincare sheaf is recovered exactly in the
line-bundle class group, along its actual mixed-product map. -/
theorem poincareLine_originalRecovery (i : C.I₀) :
    Line.Bundles.LineBundle.pullbackClass (poincareLineOriginalMap C F hN e i)
      (Line.Bundles.LineBundle.classOf (poincareLine C F hN e)) = Line.Bundles.LineBundle.classOf (F i).dual.poincare :=
  (Line.Bundles.LineBundle.pullbackClass_comp (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincareComparison C F hN e i).hom
    (PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterInclusion C F hN e i ▷ (A).scheme).left _).trans
      ((congrArg (Line.Bundles.LineBundle.pullbackClass (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincareComparison C F hN e i).hom)
        (poincareLine_recovery_class C F hN e i)).trans
          (ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincare_recovery_class (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareLineObject.DirectedPolarizedSchemeGluing
