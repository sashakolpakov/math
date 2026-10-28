import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphParameterUniversality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ParameterPointRecovery

/-! # Graph Parameter Point Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphParameterPointEquivalence

noncomputable section

/-! Points of the actual quasi-projective graph parameter are equivalent to all test-scheme morphisms with the prescribed graph Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance graphPointEquivPullbackSmooth {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [Smooth A.hom] :
    Smooth ((Over.pullback f).obj A).hom := inferInstanceAs (Smooth (Limits.pullback.snd A.hom f))

local instance graphPointEquivPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (A : Over S) [IsSeparated A.hom] :
    IsSeparated ((Over.pullback f).obj A).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd A.hom f))

variable {S : Scheme.{u}} [IsNoetherian S] {T : Over S} {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

theorem smoothEmbeddedGraphParameterClassifier_surjective :
    Function.Surjective (fun p => GraphClassifierLift.smoothEmbeddedGraphParameterClassifier (T := T) j P p) := by
  intro y
  let e := EmbeddedGraphParameters.smoothEmbeddedGraphParameterPointEquiv j P T
  let c : T ⟶ SmoothHilbert.Parameter.smoothHilbertParameter S n P := (e y).val
  have hc : c = y ≫ EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P := Graph.ParameterPointProjection.smoothEmbeddedGraphParameterPointEquiv_val j P T y
  obtain ⟨p, hp, _⟩ := (Graph.ParameterPointRecovery.graphParameter_factorization_iff_existsUnique
    (SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).family c j).mp (e y).property
  have hpoly : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p := by
    intro K _ x
    rw [hp]
    exact ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback c.left).fieldHilbert K x
  let q := (⟨p, hpoly⟩ : {p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B //
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p})
  have hy : (GraphParameterUniversality.smoothEmbeddedGraphUniversalFamily j P).pullback y.left =
      Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P q := by
    apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
    have hcomp := congrArg RelativeProjective.Families.RelativeProjectiveHilbertFamily.family
      ((SmoothHilbert.Parameter.smoothHilbertUniversalFamily S n P).pullback_comp (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left y.left)
    have hc' : c.left = y.left ≫ (EmbeddedGraphParameters.smoothEmbeddedGraphParameterHilbertMap j P).left := congrArg Over.Hom.left hc
    rw [← hc'] at hcomp
    exact hcomp.trans hp.symm
  exact ⟨q, (GraphParameterUniversality.smoothEmbeddedGraphParameterClassifier_family_existsUnique j P q).unique
    (GraphParameterUniversality.smoothEmbeddedGraphParameterClassifier_classifies j P q) hy⟩

def smoothEmbeddedGraphParameterMorphismEquiv (T : Over S) :
    (T ⟶ EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) ≃
      {p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B //
        Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P p} :=
  (Equiv.ofBijective (fun p => GraphClassifierLift.smoothEmbeddedGraphParameterClassifier (T := T) j P p)
    ⟨GraphClassifierLift.smoothEmbeddedGraphParameterClassifier_injective j P, smoothEmbeddedGraphParameterClassifier_surjective j P⟩).symm

theorem smoothEmbeddedGraphParameterMorphismEquiv_classifies (T : Over S) (y : T ⟶ EmbeddedGraphParameters.smoothEmbeddedGraphParameter j P) :
    (GraphParameterUniversality.smoothEmbeddedGraphUniversalFamily j P).pullback y.left =
      Embedded.GraphHilbertBaseChange.embeddedGraphHilbertFamily (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P
        (smoothEmbeddedGraphParameterMorphismEquiv j P T y) := by
  have he := (smoothEmbeddedGraphParameterMorphismEquiv j P T).symm_apply_apply y
  change GraphClassifierLift.smoothEmbeddedGraphParameterClassifier j P (smoothEmbeddedGraphParameterMorphismEquiv j P T y) = y at he
  have h := GraphParameterUniversality.smoothEmbeddedGraphParameterClassifier_classifies j P (smoothEmbeddedGraphParameterMorphismEquiv j P T y)
  rwa [he] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphParameterPointEquivalence
