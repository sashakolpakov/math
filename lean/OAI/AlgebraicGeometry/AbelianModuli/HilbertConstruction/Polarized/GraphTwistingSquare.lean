import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphTwistingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Graph Twisting Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphTwistingSquare

noncomputable section

/-! The twisting bundle of every polarized isomorphism graph is the square of the twisting bundle of the zero graph, including after arbitrary base changes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle B.graphBundle)
  (A.abelian.scheme ⊗ B.abelian.scheme).hom) (f : T ⟶ S)

def polarizedZeroGraphTwistingBundle : Line.Bundles.LineBundle (A.pullback f).abelian.scheme.left :=
  (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
    (MorphismGraphFamilies.familyGraph (1 : (A.pullback f).abelian.scheme ⟶ (B.pullback f).abelian.scheme) ≫
      RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (E.relativeMorphism A.graphBundle B.graphBundle)).left

theorem polarizedZeroGraphTwistingBundle_class :
    Line.Bundles.LineBundle.classOf (polarizedZeroGraphTwistingBundle A B E f) =
      Line.Bundles.LineBundle.classOf (A.pullback f).graphBundle ^ E.degree := by
  let C := A.pullback f
  let D := B.pullback f
  let z : C.abelian.scheme ⟶ D.abelian.scheme := 1
  have hz : (D.graphBundle.pullback z.left).sheaf ≅ Line.Bundles.structureModule C.abelian.scheme.left :=
    (Scheme.Modules.pullbackComp C.abelian.scheme.hom η[D.abelian.scheme].left).symm.app D.graphBundle.sheaf ≪≫
      (Scheme.Modules.pullback C.abelian.scheme.hom).mapIso D.graphBundle_zeroIso ≪≫
      Line.Bundles.structureModulePullbackIso C.abelian.scheme.hom
  have hclass : Line.Bundles.LineBundle.classOf (D.graphBundle.pullback z.left) = 1 := Quotient.sound ⟨hz⟩
  have h : Line.Bundles.LineBundle.classOf (polarizedZeroGraphTwistingBundle A B E f) =
      Line.Bundles.LineBundle.classOf ((C.graphBundle.tensor (D.graphBundle.pullback z.left)).tensorPower E.degree) :=
    Quotient.sound ⟨GraphTwistingBaseChange.polarizedGraphTwistingBundleIso A B E f z⟩
  rw [Line.Bundles.LineBundle.classOf_tensorPower, Line.Bundles.LineBundle.classOf_tensor, hclass, mul_one] at h
  exact h

def polarizedIsoGraphTwistingSquareIso
    (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback f)) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
      (MorphismGraphFamilies.familyGraph e.abelian.hom ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f
        (E.relativeMorphism A.graphBundle B.graphBundle)).left).sheaf ≅
      ((polarizedZeroGraphTwistingBundle A B E f).tensorPower 2).sheaf := by
  apply Classical.choice
  apply Line.Bundles.LineBundle.iso_tensorPower_of_class_eq
  have h : Line.Bundles.LineBundle.classOf ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
      (MorphismGraphFamilies.familyGraph e.abelian.hom ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f
        (E.relativeMorphism A.graphBundle B.graphBundle)).left) =
      Line.Bundles.LineBundle.classOf (((A.pullback f).graphBundle.tensor (A.pullback f).graphBundle).tensorPower E.degree) :=
    Quotient.sound ⟨GraphTwistingBaseChange.polarizedIsoGraphTwistingBundleIso A B E f e⟩
  rw [Line.Bundles.LineBundle.classOf_tensorPower, Line.Bundles.LineBundle.classOf_tensor] at h
  rw [h, polarizedZeroGraphTwistingBundle_class]
  simp only [pow_two, mul_pow]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphTwistingSquare
