import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.SmoothMorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkNeighborhood
import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields
import Mathlib.RingTheory.Etale.Field

/-! # Etale Morphism -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.EtaleMorphism

noncomputable section

/-! A dominant generically finite morphism of integral schemes in
characteristic zero is etale on an actual nonempty source open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields.Construction

variable {K : Type} [Field K] [CharZero K] {X Y : Scheme}
  [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType g]
  (hη : f (genericPoint X) = genericPoint Y)
  (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g))

include g hη hd in
theorem generic_formallyEtale : (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  let : Algebra K Y.functionField := Stalk.PointAlgebra.scalarAlgebra g (genericPoint Y)
  let : CharZero Y.functionField := charZero_of_injective_algebraMap (algebraMap K Y.functionField).injective
  let : Algebra Y.functionField X.functionField := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let : Module.Finite Y.functionField X.functionField := Cycles.Functoriality.FunctionFields.Construction.genericField_extension_finite f hη g hd
  have he : (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.FormallyEtale :=
    Algebra.FormallyEtale.of_isSeparable Y.functionField X.functionField
  rw [ProjectionFormula.Etale.StalkNeighborhood.ringHom_iff] at he ⊢
  exact ⟨(RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
      (Y.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom (f.stalkMap (genericPoint X))).mp he.1,
    SmoothMorphism.generic_formallySmooth f g hη⟩

include g hη hd in
theorem exists_open : ∃ U : X.Opens, genericPoint X ∈ U ∧ Etale (U.ι ≫ f) :=
  ProjectionFormula.Etale.StalkNeighborhood.exists_open f (genericPoint X) (generic_formallyEtale f g hη hd)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.EtaleMorphism
