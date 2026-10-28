import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLimit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.FrameCover
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Coefficient Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientFrames

noncomputable section

/-! An actual line bundle on a constant proper family admits a
finite affine frame cover descended to a finite coefficient algebra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

abbrev finiteCoefficientFamilyDiagram (X : Over (Spec (.of k))) :=
  CoefficientLimit.finiteCoefficientOverDiagram k R ⋙ Over.pullback X.hom ⋙ Over.forget X.left

instance finiteCoefficientOverDiagram_affine (s : (Finset R)ᵒᵖ) :
    IsAffine ((CoefficientLimit.finiteCoefficientOverDiagram k R).obj s).left :=
  inferInstanceAs (IsAffine (Spec (.of (CoefficientDiagram.finiteCoefficientRing k R s.unop))))

instance finiteCoefficientFamily_transitionAffine (X : Over (Spec (.of k)))
    {s t : (Finset R)ᵒᵖ} (f : s ⟶ t) :
    IsAffineHom ((finiteCoefficientFamilyDiagram k R X).map f) := by
  exact MorphismProperty.overPullbackMap (P := @IsAffineHom) X.hom
    ((CoefficientLimit.finiteCoefficientOverDiagram k R).map f) (isAffineHom_of_isAffine _)

instance finiteCoefficientFamily_noetherian [IsNoetherianRing k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] (s : (Finset R)ᵒᵖ) :
    IsLocallyNoetherian ((finiteCoefficientFamilyDiagram k R X).obj s) := by
  change IsLocallyNoetherian (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k (CoefficientDiagram.finiteCoefficientRing k R s.unop)))) X.hom)
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst
    (Spec.map (CommRingCat.ofHom (algebraMap k (CoefficientDiagram.finiteCoefficientRing k R s.unop)))) X.hom)

instance finiteCoefficientFamily_compact (X : Over (Spec (.of k))) [QuasiCompact X.hom]
    (s : (Finset R)ᵒᵖ) : CompactSpace ((finiteCoefficientFamilyDiagram k R X).obj s) := by
  change CompactSpace (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k (CoefficientDiagram.finiteCoefficientRing k R s.unop)))) X.hom : Scheme.{u})
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst
    (Spec.map (CommRingCat.ofHom (algebraMap k (CoefficientDiagram.finiteCoefficientRing k R s.unop)))) X.hom)

theorem exists_finite_coefficient_family_frame_cover [IsNoetherianRing k]
    (X : Over (Spec (.of k))) [IsProper X.hom]
    (L : HilbertConstruction.Line.Bundles.LineBundle (CoefficientLimit.algebraSpecOver k R ⊗ X).left) :
    ∃ (s : Finset R) (n : ℕ)
      (V : Fin n → ((finiteCoefficientFamilyDiagram k R X).obj (.op s)).Opens),
      IsOpenCover V ∧ (∀ j, IsAffineOpen (V j)) ∧
      (∀ j, Nonempty ((Scheme.Modules.pullback
        ((CoefficientLimit.finiteCoefficientFamilyCone k R X).π.app (.op s) ⁻¹ᵁ V j).ι).obj L.sheaf ≅
          HilbertConstruction.Line.Bundles.structureModule ((CoefficientLimit.finiteCoefficientFamilyCone k R X).π.app (.op s) ⁻¹ᵁ V j).toScheme)) := by
  classical
  obtain ⟨i, n, V, hV, ha, he⟩ := InverseLimit.FrameCover.exists_limit_line_frame_cover_stage
    (finiteCoefficientFamilyDiagram k R X) (CoefficientLimit.finiteCoefficientFamilyCone k R X)
    (CoefficientLimit.finiteCoefficientFamilyCone_isLimit k R X) L
  exact ⟨i.unop, n, V, hV, ha, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientFrames
