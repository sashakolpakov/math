import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SubfunctorRepresentations

/-! # Parameter Iso Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ParameterIsoFactorization

noncomputable section

/-! Parameter conditions and factorization through a representing map
are invariant under isomorphisms of test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {T U M Z : Over S}

theorem subfunctor_mem_comp_iso_iff (F : Subfunctor (yoneda.obj M)) (e : U ≅ T) (x : T ⟶ M) :
    e.hom ≫ x ∈ F.obj (.op U) ↔ x ∈ F.obj (.op T) := by
  constructor
  · intro h
    have hh := F.map e.inv.op h
    change e.inv ≫ (e.hom ≫ x) ∈ F.obj (.op T) at hh
    simpa only [Iso.inv_hom_id_assoc] using hh
  · intro h
    exact F.map e.hom.op h

theorem exists_lift_comp_iso_iff (e : U ≅ T) (j : Z ⟶ M) (x : T ⟶ M) :
    (∃ y : U ⟶ Z, y ≫ j = e.hom ≫ x) ↔ ∃ y : T ⟶ Z, y ≫ j = x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.inv ≫ y, ?_⟩
    rw [Category.assoc, hy, Iso.inv_hom_id_assoc]
  · rintro ⟨y, hy⟩
    exact ⟨e.hom ≫ y, (Category.assoc _ _ _).trans (congrArg (fun f => e.hom ≫ f) hy)⟩

theorem over_exists_lift_iff_left (j : Z ⟶ M) (x : T ⟶ M) :
    (∃ y : T ⟶ Z, y ≫ j = x) ↔ ∃ y : T.left ⟶ Z.left, y ≫ j.left = x.left := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.left, congrArg Over.Hom.left hy⟩
  · rintro ⟨y, hy⟩
    have hw : y ≫ Z.hom = T.hom := by
      rw [← j.w, ← Category.assoc, hy]
      exact x.w
    exact ⟨Over.homMk y hw, Over.OverMorphism.ext hy⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ParameterIsoFactorization
