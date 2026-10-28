import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Quotient Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientPoints

noncomputable section

/-! The actual quotient spectrum over an affine base represents the
vanishing of its defining ideal on every test scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction

universe u

def affineQuotientScheme (S : Scheme.{u}) [IsAffine S] (I : Ideal Γ(S, ⊤)) : Over S :=
  OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraScheme S (CommAlgCat.of Γ(S, ⊤) (Γ(S, ⊤) ⧸ I))

instance affineQuotientScheme_closedImmersion (S : Scheme.{u}) [IsAffine S]
    (I : Ideal Γ(S, ⊤)) : IsClosedImmersion (affineQuotientScheme S I).hom := by
  have : IsClosedImmersion (Spec.map (OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.affineBaseAlgebraMap S
      (CommAlgCat.of Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  change IsClosedImmersion (Spec.map _ ≫ S.isoSpec.inv)
  infer_instance

theorem affineQuotientScheme_hasLift_iff (S : Scheme.{u}) [IsAffine S]
    (I : Ideal Γ(S, ⊤)) (T : Over S) :
    Nonempty (T ⟶ affineQuotientScheme S I) ↔ I ≤ RingHom.ker T.hom.appTop.hom := by
  let : Algebra Γ(S, ⊤) Γ(T.left, ⊤) := T.hom.appTop.hom.toAlgebra
  let e := OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S (CommAlgCat.of Γ(S, ⊤) (Γ(S, ⊤) ⧸ I)) T
  constructor
  · rintro ⟨p⟩ a ha
    change T.hom.appTop a = 0
    have hz : algebraMap Γ(S, ⊤) (Γ(S, ⊤) ⧸ I) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    calc
      T.hom.appTop a = e p (algebraMap Γ(S, ⊤) (Γ(S, ⊤) ⧸ I) a) :=
        ((e p).commutes a).symm
      _ = 0 := by rw [hz, map_zero]
  · intro h
    exact ⟨e.symm (Ideal.Quotient.liftₐ I (Algebra.ofId Γ(S, ⊤) Γ(T.left, ⊤)) h)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientPoints
