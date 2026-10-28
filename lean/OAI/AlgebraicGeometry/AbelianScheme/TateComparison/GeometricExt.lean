import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Neighbors
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt

noncomputable section

/-! Actual morphisms from a reduced scheme to a separated scheme are
determined by their points over algebraically closed fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem over_hom_ext_geometric {S : Scheme.{u}} {X Y : Over S}
    [IsReduced X.left] [IsSeparated Y.hom] (f g : X ⟶ Y)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ S) (x : Over.mk b ⟶ X), x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq f.left g.left Y.hom Set.univ dense_univ
  · intro x _
    let k := AlgebraicClosure (X.left.residueField x)
    let p : Spec (.of k) ⟶ Spec (X.left.residueField x) :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) k))
    have : Flat p := inferInstance
    have : Surjective p := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
    have : Epi p := Flat.epi_of_flat_of_surjective p
    let a := p ≫ X.left.fromSpecResidueField x
    let b := a ≫ X.hom
    let z : Over.mk b ⟶ X := Over.homMk a rfl
    have hz := congrArg (fun z => z.left) (h k b z)
    apply (cancel_epi p).mp
    simpa only [z, a, Over.homMk_left, Over.comp_left, Category.assoc] using hz
  · exact f.w.trans g.w.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
