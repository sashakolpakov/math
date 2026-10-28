import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.GroupMarkingDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGroupPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange

/-! # Constant Subgroups -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ConstantSubgroups

noncomputable section

/-! Construct an actual closed finite subgroup over a finite number-field
extension from a finite group of complex points in an arithmetic finite
étale group scheme. The construction retains every original complex
coordinate, through the specified field embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

def markingOverField {k : Type} [Field k] {S : Scheme} (φ : Spec (.of k) ⟶ S)
    (H : Over S) [GrpObj H] {G : Type} [Group G] (a : G →* (Over.mk φ ⟶ H)) :
    G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest (Spec (.of k)) ⟶ (Over.pullback φ).obj H) :=
  (FieldGroupPoints.fieldGroupPointsMulEquiv φ H).symm.toMonoidHom.comp a

theorem markingOverField_fst {k : Type} [Field k] {S : Scheme}
    (φ : Spec (.of k) ⟶ S) (H : Over S) [GrpObj H] {G : Type} [Group G]
    (a : G →* (Over.mk φ ⟶ H)) (g : G) :
    (markingOverField φ H a g).left ≫ pullback.fst H.hom φ = (a g).left :=
  FieldGroupPoints.fieldGroupPointsMulEquiv_symm_fst φ H (a g)

theorem markingOverField_distinct {k : Type} [Field k] {S : Scheme}
    (φ : Spec (.of k) ⟶ S) (H : Over S) [GrpObj H] {G : Type} [Group G]
    (a : G →* (Over.mk φ ⟶ H))
    (ha : AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Distinct H G a) :
    AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Distinct ((Over.pullback φ).obj H) G
      (markingOverField φ H a) := by
  intro L hL s t x y hxy
  have ht : t.left = s := (Category.comp_id t.left).symm.trans t.w
  let tS : Over.mk (s ≫ φ) ⟶ Over.mk φ := Over.homMk t.left (by rw [ht]; rfl)
  apply ha L (s ≫ φ) tS
  apply Over.OverMorphism.ext
  have h := congrArg (fun u => u.left ≫ pullback.fst H.hom φ) hxy
  change (t.left ≫ (markingOverField φ H a x).left) ≫ pullback.fst H.hom φ =
    (t.left ≫ (markingOverField φ H a y).left) ≫ pullback.fst H.hom φ at h
  rw [Category.assoc, Category.assoc, markingOverField_fst, markingOverField_fst] at h
  exact h

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (H : Over (Spec (.of K))) [GrpObj H] [IsFinite H.hom] [Etale H.hom]
  (G : Type) [Group G] [Finite G]

/-- The descended group is the actual finite disjoint union of copies of
the extension field, with its constructed group law and closed embedding
into the base-changed arithmetic group scheme. -/
theorem arithmetic_closed_constant_subgroup
    (a : G →* (Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ H))
    (ha : Function.Injective a) (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ)
      (j : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G ⟶
        (Over.pullback B.fieldExtension).obj H),
      B.denominator = N ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧
        IsFinite (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ∧
        Etale (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ∧
        ∀ g : G, Spec.map (CommRingCat.ofHom B.embedding) ≫
          (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component (Spec (.of B.extension.carrier)) g ≫ j).left ≫
            pullback.fst H.hom B.fieldExtension = (a g).left := by
  obtain ⟨B, aL, hBN, _, hdistinct, hvalues⟩ := IntegralModel.Finite.GroupMarkingDescent.finite_group_marking_descends κ H G a ha N hN
  let hL := markingOverField B.fieldExtension H aL
  have hLdistinct : AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Distinct
      ((Over.pullback B.fieldExtension).obj H) G hL :=
    markingOverField_distinct B.fieldExtension H aL hdistinct
  let j := AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑hL)
  have : IsFinite ((Over.pullback B.fieldExtension).obj H).hom :=
    inferInstanceAs (IsFinite (pullback.snd H.hom B.fieldExtension))
  have : Etale ((Over.pullback B.fieldExtension).obj H).hom :=
    inferInstanceAs (Etale (pullback.snd H.hom B.fieldExtension))
  obtain ⟨hj, hf, he, hg, hlabels⟩ := ConstantBaseChange.ConstantGroupModels.constant_subgroup_closed hL hLdistinct
  refine ⟨B, j, hBN, hg, hj, hf, he, ?_⟩
  intro g
  have hpoint : (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component (Spec (.of B.extension.carrier)) g ≫ j).left = (hL g).left :=
    congrArg Over.Hom.left (hlabels g)
  rw [hpoint]
  exact (congrArg (fun f => Spec.map (CommRingCat.ofHom B.embedding) ≫ f)
    (markingOverField_fst B.fieldExtension H aL g)).trans
      (congrArg Over.Hom.left (hvalues g))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ConstantSubgroups
