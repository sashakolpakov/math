import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType

/-! # Projective Proper -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveProper

noncomputable section

/-! The relative polynomial projective spectrum is proper over its
coefficient scheme, with its actual degree-zero structure map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Base

variable (R : Type) [CommRing R] (n : ℕ)

instance finiteType_zero : Algebra.FiniteType (ProjectiveLinear.grading R n 0) (MvPolynomial (Fin (n + 1)) R) := by
  let : IsScalarTower R (ProjectiveLinear.grading R n 0) (MvPolynomial (Fin (n + 1)) R) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := ProjectiveLinear.grading R n 0)
      (A := MvPolynomial (Fin (n + 1)) R) (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (ProjectiveLinear.grading R n 0) (MvPolynomial (Fin (n + 1)) R)

instance constants_iso : IsIso (Spec.map (CommRingCat.ofHom (ProjectiveI.Base.constants R n).toRingHom)) := by
  change IsIso (Scheme.Spec.mapIso (ProjectiveI.Base.constants R n).toCommRingCatIso.op).hom
  infer_instance

instance proper : IsProper (ProjectiveI.Base.base R n) := by
  unfold ProjectiveI.Base.base
  infer_instance

instance noetherian [IsNoetherianRing R] : AlgebraicGeometry.IsNoetherian (ProjectiveLinear.space R n) where
  __ := LocallyOfFiniteType.isLocallyNoetherian (ProjectiveI.Base.base R n)
  __ := QuasiCompact.compactSpace_of_compactSpace (ProjectiveI.Base.base R n)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveProper
