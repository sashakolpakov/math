import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt

/-! # Over Coproduct -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.OverCoproduct

noncomputable section

/-! Explicit coproducts of schemes over a base, and factorization of
field-valued points through one component. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme.{0}} {I : Type} (U : I → Over B)

abbrev overCoproduct : Over B := Over.mk (Sigma.desc (fun i => (U i).hom))

def overCoproductι (i : I) : U i ⟶ overCoproduct U :=
  Over.homMk (Sigma.ι (fun i => (U i).left) i) (Sigma.ι_comp_desc _ _)

def overCoproductDesc {Y : Over B} (f : ∀ i, U i ⟶ Y) : overCoproduct U ⟶ Y :=
  Over.homMk (Sigma.desc (fun i => (f i).left)) (by
    change Sigma.desc (fun i => (f i).left) ≫ Y.hom = Sigma.desc (fun i => (U i).hom)
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (f i).w)

theorem overCoproductι_desc {Y : Over B} (f : ∀ i, U i ⟶ Y) (i : I) :
    overCoproductι U i ≫ overCoproductDesc U f = f i := by
  apply Over.OverMorphism.ext
  exact Sigma.ι_comp_desc _ _

/-- A field-valued point of a scheme coproduct factors through a single
component as an actual scheme morphism. -/
theorem overCoproduct_point_factor {k : Type} [Field k] (b : Spec (.of k) ⟶ B)
    (a : Over.mk b ⟶ overCoproduct U) :
    ∃ i : I, ∃ ai : Over.mk b ⟶ U i, ai ≫ overCoproductι U i = a := by
  let : Unique (Over.mk b).left := inferInstanceAs (Unique (Spec (.of k)))
  obtain ⟨⟨i, t⟩, ht⟩ := (sigmaMk (fun i => (U i).left)).surjective (a.left default)
  have hi : Sigma.ι (fun i => (U i).left) i t = a.left default :=
    (sigmaMk_mk (fun i => (U i).left) i t).symm.trans ht
  have hrange : Set.range a.left ⊆ Set.range (Sigma.ι (fun i => (U i).left) i) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨t, hi.trans (congrArg a.left (Subsingleton.elim _ _))⟩
  let ai := IsOpenImmersion.lift (Sigma.ι (fun i => (U i).left) i) a.left hrange
  have hai : ai ≫ Sigma.ι (fun i => (U i).left) i = a.left :=
    IsOpenImmersion.lift_fac _ _ _
  have hbase : ai ≫ (U i).hom = b := by
    calc
      _ = (ai ≫ Sigma.ι (fun i => (U i).left) i) ≫ (overCoproduct U).hom := by
        change ai ≫ (U i).hom =
          (ai ≫ Sigma.ι (fun i => (U i).left) i) ≫ Sigma.desc (fun j => (U j).hom)
        rw [Category.assoc, Sigma.ι_comp_desc]
      _ = b := by rw [hai]; exact a.w
  refine ⟨i, Over.homMk ai hbase, ?_⟩
  apply Over.OverMorphism.ext
  exact hai

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.OverCoproduct
