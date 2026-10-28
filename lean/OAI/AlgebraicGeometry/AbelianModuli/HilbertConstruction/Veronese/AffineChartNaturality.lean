import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.SchemeMorphism

/-! # Affine Chart Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.AffineChartNaturality

noncomputable section

/-! The global Veronese scheme morphism restricts to the explicitly
constructed isomorphism of each homogeneous affine chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

theorem veronese_ι_comp_map (f : Subalgebra.veroneseSubalgebra g N) :
    (Proj.basicOpen g f.val).ι ≫ SchemeMorphism.veroneseSchemeMorphism g N =
      (SchemeMorphism.veroneseSchemeMorphism g N).resLE _ _ le_rfl ≫ (Proj.basicOpen (Grading.veroneseGrading g N) f).ι := by
  exact (Scheme.Hom.resLE_comp_ι (U := Proj.basicOpen (Grading.veroneseGrading g N) f)
    (V := Proj.basicOpen g f.val) (SchemeMorphism.veroneseSchemeMorphism g N) le_rfl).symm

theorem veronese_awayToSection_comp_appLE {d : ℕ}
    (f : Subalgebra.veroneseSubalgebra g N) (hf : f ∈ Grading.veroneseGrading g N d) :
    Proj.awayToSection (Grading.veroneseGrading g N) f ≫
        Scheme.Hom.appLE (SchemeMorphism.veroneseSchemeMorphism g N)
          (Proj.basicOpen (Grading.veroneseGrading g N) f) (Proj.basicOpen g f.val) (by rfl) =
      CommRingCat.ofHom (AffineChartEquivalence.veroneseAwayMap g N f) ≫ Proj.awayToSection g f.val := by
  ext x
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (Grading.veroneseGrading g N) hf x
  refine Subtype.ext (funext fun p => ?_)
  apply HomogeneousLocalization.val_injective
  rfl

theorem veronese_awayι_comp_map {d : ℕ} (hd : 0 < d)
    (f : Subalgebra.veroneseSubalgebra g N) (hf : f ∈ Grading.veroneseGrading g N d) :
    Proj.awayι g f.val hf (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) hd) ≫
        SchemeMorphism.veroneseSchemeMorphism g N =
      Spec.map (CommRingCat.ofHom (AffineChartEquivalence.veroneseAwayMap g N f)) ≫
        Proj.awayι (Grading.veroneseGrading g N) f hf hd := by
  simp only [Proj.awayι]
  rw [Category.assoc, veronese_ι_comp_map,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec ((cancel_mono (Proj.basicOpen g f.val).topIso.hom).mp ?_)
  simp [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
    veronese_awayToSection_comp_appLE g N f hf]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.AffineChartNaturality
