import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient
import Mathlib.Algebra.Polynomial.Eval.Algebra

/-! # Parameter -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global deformation parameter and the graph deformation

The local elements t agree under coefficient restriction, so they give a
global morphism from the glued deformation to the affine integer line. The
graph deformation uses the actual kernel ideal sheaf of the closed graph.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- The parameter line, with integers lifted only to match the scheme universe. -/
def deformationParameterLine : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The integer polynomial variable evaluates to the actual deformation parameter. -/
def deformationParameterRingMap (I : Ideal R) :
    Polynomial (ULift.{u} ℤ) →+* Iff.BundleCycles.deformationAlgebra I :=
  Polynomial.eval₂RingHom
    ((Int.castRingHom (Iff.BundleCycles.deformationAlgebra I)).comp ULift.ringEquiv.toRingHom)
    (Iff.BundleCycles.deformationParameter I)

@[simp]
theorem deformationParameterRingMap_X (I : Ideal R) :
    deformationParameterRingMap I Polynomial.X = Iff.BundleCycles.deformationParameter I :=
  Polynomial.eval₂_X _ _

theorem deformationParameterRingMap_natural (I : Ideal R) (J : Ideal S)
    (f : R →+* S) (hf : I ≤ J.comap f) :
    (Maps.BundleCycles.deformationMap I J f hf).comp (deformationParameterRingMap I) =
      deformationParameterRingMap J := by
  apply Polynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, deformationParameterRingMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change Maps.BundleCycles.deformationMap I J f hf (z.down : Iff.BundleCycles.deformationAlgebra I) =
      (z.down : Iff.BundleCycles.deformationAlgebra J)
    exact map_intCast _ _
  · change Maps.BundleCycles.deformationMap I J f hf (deformationParameterRingMap I Polynomial.X) =
      deformationParameterRingMap J Polynomial.X
    rw [deformationParameterRingMap_X, deformationParameterRingMap_X,
      Maps.BundleCycles.deformationMap_parameter]

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Compatible parameter morphisms on all affine deformation charts. -/
def deformationParameterCocone : Cocone (Global.Deformation.BundleCycles.deformationGlueData I).functor where
  pt := deformationParameterLine
  ι.app U := Spec.map (CommRingCat.ofHom (deformationParameterRingMap (I.ideal U)))
  ι.naturality {U V} f := by
    have h : CommRingCat.ofHom (deformationParameterRingMap (I.ideal V)) ≫
        (Global.Deformation.BundleCycles.deformationDiagram I).map f.op =
          CommRingCat.ofHom (deformationParameterRingMap (I.ideal U)) := by
      apply CommRingCat.hom_ext
      exact deformationParameterRingMap_natural (I.ideal V) (I.ideal U)
        (X.presheaf.map ((toOpensFunctor X).op.map f.op)).hom
        (I.ideal_le_comap_ideal (toOpens_mono f.le))
    exact (Spec.map_comp (CommRingCat.ofHom (deformationParameterRingMap (I.ideal V)))
      ((Global.Deformation.BundleCycles.deformationDiagram I).map f.op)).symm.trans (congrArg Spec.map h)

/-- The actual global parameter morphism of the deformation scheme. -/
def globalDeformationParameter : Global.Deformation.BundleCycles.globalDeformation I ⟶ deformationParameterLine :=
  colimit.desc _ (deformationParameterCocone I)

/-- The global parameter restricts to t on each affine deformation chart. -/
theorem globalDeformationParameter_on_chart (U : X.AffineZariskiSite) :
    (Global.Deformation.BundleCycles.globalDeformationCover I).f U ≫ globalDeformationParameter I =
      Spec.map (CommRingCat.ofHom (deformationParameterRingMap (I.ideal U))) :=
  colimit.ι_desc (deformationParameterCocone I) U

variable {P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

/-- The actual ideal sheaf defining the scheme-theoretic graph. -/
def graphIdeal (f : P.toOver ⟶ Q.toOver) : (Graph.OpenAmbient.BundleCycles.graphAmbient f).IdealSheafData := (Graph.OpenAmbient.BundleCycles.graph f).ker

/-- Deformation of the ambient product along the actual graph ideal. -/
def graphDeformation (f : P.toOver ⟶ Q.toOver) : Scheme := Global.Deformation.BundleCycles.globalDeformation (graphIdeal f)

/-- Projection of the graph deformation to the original ambient product. -/
def graphDeformationProjection (f : P.toOver ⟶ Q.toOver) :
    graphDeformation f ⟶ Graph.OpenAmbient.BundleCycles.graphAmbient f := Global.Deformation.BundleCycles.globalDeformationProjection (graphIdeal f)

/-- The graph deformation's global parameter. -/
def graphDeformationParameter (f : P.toOver ⟶ Q.toOver) :
    graphDeformation f ⟶ deformationParameterLine := globalDeformationParameter (graphIdeal f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Parameter.BundleCycles
