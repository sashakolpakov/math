import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra
import Mathlib.RingTheory.Smooth.Field

/-! # Smooth Morphism -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.SmoothMorphism

noncomputable section

/-! A dominant morphism of integral schemes over a characteristic-zero
field is smooth on an actual nonempty source open. The proof uses its
native generic stalk map and the native open smooth locus. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [CharZero K] {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  (g : Y ⟶ Spec (.of K)) (hη : f (genericPoint X) = genericPoint Y)

include g hη in
theorem generic_formallySmooth : (f.stalkMap (genericPoint X)).hom.FormallySmooth := by
  let R := Y.presheaf.stalk (f (genericPoint X))
  have hR : IsField R := by
    change IsField (Y.presheaf.stalk (f (genericPoint X)))
    rw [hη]
    exact Field.toIsField Y.functionField
  let : Field R := hR.toField
  let : Algebra K R := Stalk.PointAlgebra.scalarAlgebra g (f (genericPoint X))
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap K R).injective
  let : Algebra R X.functionField := (f.stalkMap (genericPoint X)).hom.toAlgebra
  let : Algebra.EssFiniteType R X.functionField := LocallyOfFiniteType.stalkMap f (genericPoint X)
  exact Algebra.FormallySmooth.of_perfectField

include g hη in
theorem generic_mem : genericPoint X ∈ f.smoothLocus := generic_formallySmooth f g hη

omit [IsIntegral X] [IsIntegral Y] in
theorem smooth_restrict : Smooth (f.smoothLocus.ι ≫ f) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  change x.val ∈ f.smoothLocus ↔ True
  exact iff_true_intro x.property

include g hη in
theorem exists_open : ∃ U : X.Opens, genericPoint X ∈ U ∧ Smooth (U.ι ≫ f) :=
  ⟨f.smoothLocus, generic_mem f g hη, smooth_restrict f⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.SmoothMorphism
