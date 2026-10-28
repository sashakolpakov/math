import OAI.AlgebraicGeometry.Albanese.Construction.EtaleGeneric
import OAI.AlgebraicGeometry.Albanese.Construction.GeneratingWords
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Finite Refinements -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.FiniteRefinements

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Equal-dimensional refinements of generated targets are étale. -/
theorem refinement_etale (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (b : X.toOver ⟶ B.toOver)
    (φ : A.toOver ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b)
    (hb : GeneratedClosed.Generates X B b)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap) : Etale φ.left := by
  have : IsIntegral A.toOver.left := inferInstanceAs (IsIntegral A.carrier)
  have : IsIntegral B.toOver.left := inferInstanceAs (IsIntegral B.carrier)
  have : Surjective φ.left := GeneratedClosed.refinement_surjective X A B a b φ hφ hb
  have : IsDominant φ.left := ⟨φ.left.surjective.denseRange⟩
  have : Smooth φ.left := DominantSmooth.refinement_smooth X A B a b φ hφ hb
  have : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  have : LocallyOfFiniteType B.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType B.variety.structureMap)
  have : LocallyOfFiniteType (φ.left ≫ B.toOver.hom) := by rw [φ.w]; infer_instance
  apply EtaleGeneric.smooth_etale_of_dimension_eq φ.left B.toOver.hom
  rw [φ.w]
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap
  exact hd

/-- Étale morphisms have quasi-finite fibers. -/
theorem etale_locallyQuasiFinite {A B : Scheme} (f : A ⟶ B) [Etale f] :
    LocallyQuasiFinite f where
  quasiFinite_appLE {U} hU {V} hV e := by
    have := f.etale_appLE hU hV e
    algebraize [(f.appLE _ _ e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite Γ(B, U) Γ(A, V))

/-- Properness upgrades an equal-dimensional refinement to a finite map. -/
theorem refinement_finite (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (b : X.toOver ⟶ B.toOver)
    (φ : A.toOver ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b)
    (hb : GeneratedClosed.Generates X B b)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap) : IsFinite φ.left := by
  have : Etale φ.left := refinement_etale X A B a b φ hφ hb hd
  have : LocallyQuasiFinite φ.left := etale_locallyQuasiFinite φ.left
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsProper B.toOver.hom := B.variety.presentation.projective.isProper
  have : IsProper (φ.left ≫ B.toOver.hom) := by rw [φ.w]; infer_instance
  have : IsProper φ.left := IsProper.of_comp _ B.toOver.hom
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

/-- A Hausdorff continuous image has at most as many points as the source has
irreducible components, if there are finitely many such components. -/
theorem card_le_irreducibleComponents_of_surjective
    {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T] [T2Space T]
    [Finite (irreducibleComponents Z)] (f : Z → T) (hf : Continuous f)
    (hsurj : Function.Surjective f) : Nat.card T ≤ Nat.card (irreducibleComponents Z) := by
  let point (C : irreducibleComponents Z) : Z :=
    C.property.1.nonempty.choose
  have hpoint (C : irreducibleComponents Z) : point C ∈ C.val :=
    C.property.1.nonempty.choose_spec
  apply Nat.card_le_card_of_surjective (fun C => f (point C))
  intro t
  obtain ⟨z, rfl⟩ := hsurj t
  let C : irreducibleComponents Z := ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  refine ⟨C, ?_⟩
  exact (C.property.1.image f
    hf.continuousOn).isPreirreducible.subsingleton
      ⟨point C, hpoint C, rfl⟩ ⟨z, mem_irreducibleComponent, rfl⟩

/-- Surjectivity survives taking the fibers of a factorization. -/
def factorFiberMap {D A B : Scheme.{u}} (a : D ⟶ A) (φ : A ⟶ B) (y : B) :
    (a ≫ φ).fiber y ⟶ φ.fiber y :=
  pullback.map (a ≫ φ) (B.fromSpecResidueField y) φ (B.fromSpecResidueField y)
    a (𝟙 _) (𝟙 _) (by simp) (by simp)

theorem factorFiberMap_surjective {D A B : Scheme.{u}} (a : D ⟶ A) (φ : A ⟶ B)
    [Surjective a] (y : B) : Surjective (factorFiberMap a φ y) := by
  have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    ⟨fun _ _ hf hg => ⟨hg.1.comp hf.1⟩⟩
  unfold factorFiberMap
  exact MorphismProperty.pullbackMap (P := @Surjective.{u})
    (f := a ≫ φ) (g := B.fromSpecResidueField y) (f' := φ) (g' := B.fromSpecResidueField y)
    (inferInstance : Surjective a)
    (inferInstance : Surjective (𝟙 (Spec (B.residueField y)))) rfl (by simp)

/-- Finite-type fiber components bound the size of a quasi-finite target
fiber reached by a surjective factorization. -/
theorem fiber_card_le_components_of_factor {D A B : Scheme.{u}}
    (a : D ⟶ A) (φ : A ⟶ B) [Surjective a] [LocallyQuasiFinite φ] (y : B)
    [Finite (irreducibleComponents ((a ≫ φ).fiber y))] :
    Nat.card (φ.fiber y) ≤ Nat.card (irreducibleComponents ((a ≫ φ).fiber y)) := by
  have := factorFiberMap_surjective a φ y
  exact card_le_irreducibleComponents_of_surjective (factorFiberMap a φ y)
    (factorFiberMap a φ y).continuous (factorFiberMap a φ y).surjective

end

end OAI.AlgebraicGeometry.Albanese.Construction.FiniteRefinements
