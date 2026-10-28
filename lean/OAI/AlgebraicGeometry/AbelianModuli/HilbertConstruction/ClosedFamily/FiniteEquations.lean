import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationCancellation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families

/-! # Finite Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Closed finitely presented families have finitely many equations on each affine ambient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ClosedFamily.FiniteEquations.finitePresentation_surjective_kernel_fg
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hf : f.FinitePresentation) (hs : Function.Surjective f) : (RingHom.ker f).FG := by
  let : Algebra R A := f.toAlgebra
  let : Algebra.FinitePresentation R A := hf
  exact Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom R R A) hs

theorem ClosedFamily.FiniteEquations.closedImmersion_finitePresentation_ideal_fg
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f] (U : Y.affineOpens) : (f.ker.ideal U).FG := by
  rw [Scheme.Hom.ker_apply]
  apply ClosedFamily.FiniteEquations.finitePresentation_surjective_kernel_fg
  · rw [Scheme.Hom.app_eq_appLE]
    exact f.finitePresentation_appLE U.2 (U.2.preimage f) le_rfl
  · exact f.app_surjective U.1 U.2

theorem Closed.Families.FlatClosedFamily.inclusion_locallyFinitePresentation
    {S : Scheme.{u}} {P : Over S} [LocallyOfFiniteType P.hom]
    (F : Closed.Families.FlatClosedFamily P) : LocallyOfFinitePresentation F.inclusion.left :=
  Finite.PresentationCancellation.locallyFinitePresentation_of_comp_of_locallyFiniteType
    F.locallyFinitePresentation inferInstance

theorem Closed.Families.FlatClosedFamily.ideal_fg
    {S : Scheme.{u}} {P : Over S} [LocallyOfFiniteType P.hom]
    (F : Closed.Families.FlatClosedFamily P) (U : P.left.affineOpens) : (F.ideal.ideal U).FG := by
  let : LocallyOfFinitePresentation F.ideal.subschemeι :=
    F.inclusion_locallyFinitePresentation
  have h := ClosedFamily.FiniteEquations.closedImmersion_finitePresentation_ideal_fg F.ideal.subschemeι U
  rwa [F.ideal.ker_subschemeι] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
