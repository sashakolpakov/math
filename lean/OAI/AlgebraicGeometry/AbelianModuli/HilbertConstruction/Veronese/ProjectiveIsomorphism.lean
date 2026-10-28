import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.AffineChartNaturality
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Projective Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveIsomorphism

noncomputable section

/-! The Veronese scheme morphism is an isomorphism: its restrictions
to a covering family of target charts are the constructed ring isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

theorem veroneseSchemeMorphism_restrict_isIso {d : ℕ} (hd : 0 < d)
    (f : Subalgebra.veroneseSubalgebra g N) (hf : f ∈ Grading.veroneseGrading g N d) :
    IsIso (SchemeMorphism.veroneseSchemeMorphism g N ∣_ Proj.basicOpen (Grading.veroneseGrading g N) f) := by
  let src := Proj.basicOpenIsoSpec g f.val hf (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) hd)
  let tgt := Proj.basicOpenIsoSpec (Grading.veroneseGrading g N) f hf hd
  let a := Spec.map (CommRingCat.ofHom (AffineChartEquivalence.veroneseAwayMap g N f))
  have : IsIso (CommRingCat.ofHom (AffineChartEquivalence.veroneseAwayMap g N f)) :=
    (AffineChartEquivalence.veroneseAwayEquiv g N f hf).toCommRingCatIso.isIso_hom
  have hdiag : src.inv ≫ (SchemeMorphism.veroneseSchemeMorphism g N ∣_ Proj.basicOpen (Grading.veroneseGrading g N) f) =
      a ≫ tgt.inv := by
    apply (cancel_mono (Proj.basicOpen (Grading.veroneseGrading g N) f).ι).mp
    erw [Category.assoc, morphismRestrict_ι]
    exact AffineChartNaturality.veronese_awayι_comp_map g N hd f hf
  have hcomp : IsIso (src.inv ≫
      (SchemeMorphism.veroneseSchemeMorphism g N ∣_ Proj.basicOpen (Grading.veroneseGrading g N) f)) := by
    rw [hdiag]
    infer_instance
  exact (isIso_comp_left_iff src.inv _).mp hcomp

instance veroneseSchemeMorphism_isIso : IsIso (SchemeMorphism.veroneseSchemeMorphism g N) := by
  let U (j : ProjectiveChartCover.positiveVeroneseChartIndex g N) :=
    Proj.basicOpen (Grading.veroneseGrading g N) (ProjectiveChartCover.positiveVeroneseChartElement g N j)
  have hcover : iSup U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr (ProjectiveChartCover.veronese_regraded_charts_cover g N x)
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hcover).mpr
  intro j
  exact veroneseSchemeMorphism_restrict_isIso g N j.1.property (ProjectiveChartCover.positiveVeroneseChartElement g N j) j.2.property

def veroneseProjectiveIso : Proj g ≅ Proj (Grading.veroneseGrading g N) := asIso (SchemeMorphism.veroneseSchemeMorphism g N)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveIsomorphism
