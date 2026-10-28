import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! # Differential Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.DifferentialJet

noncomputable section

/-! The universal first-order jet of an affine complex test scheme.
Its square-zero coefficient is its actual module of Kähler differentials,
and base change uses the actual differential map. -/

open _root_.CategoryTheory

@[instance_reducible] def differentialOppositeModule (A : Type) [CommRing A] [Algebra ℂ A] :
    Module Aᵐᵒᵖ (KaehlerDifferential ℂ A) :=
  Module.compHom _ ((RingHom.id A).fromOpposite mul_comm)

attribute [local instance] differentialOppositeModule

instance differentialCentralScalar (A : Type) [CommRing A] [Algebra ℂ A] :
    IsCentralScalar A (KaehlerDifferential ℂ A) := ⟨fun _ _ => rfl⟩

abbrev differentialJetRing (R : CommAlgCat.{0} ℂ) :=
  TrivSqZeroExt R (KaehlerDifferential ℂ R)

def differentialJet (R : CommAlgCat.{0} ℂ) : R →ₐ[ℂ] differentialJetRing R where
  toFun r := (r, KaehlerDifferential.D ℂ R r)
  map_zero' := by apply TrivSqZeroExt.ext; rfl; exact map_zero _
  map_one' := by apply TrivSqZeroExt.ext; rfl; exact Derivation.map_one_eq_zero _
  map_add' r s := by apply TrivSqZeroExt.ext; rfl; exact map_add _ r s
  map_mul' r s := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact (KaehlerDifferential.D ℂ R).leibniz r s
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact (KaehlerDifferential.D ℂ R).map_algebraMap c

def differentialJetMap {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    differentialJetRing R →ₐ[ℂ] differentialJetRing S where
  toFun z := (f.hom z.fst, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f z.snd)
  map_zero' := by apply TrivSqZeroExt.ext; exact map_zero _; exact map_zero _
  map_one' := by apply TrivSqZeroExt.ext; exact map_one _; exact map_zero _
  map_add' z w := by
    apply TrivSqZeroExt.ext
    · exact map_add _ _ _
    · exact map_add _ _ _
  map_mul' z w := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f (z.fst • w.snd + w.fst • z.snd) =
        f.hom z.fst • AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f w.snd + f.hom w.fst • AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f z.snd
      rw [map_add, DifferentialNaturality.differentialMap_smul, DifferentialNaturality.differentialMap_smul]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact f.hom.commutes c
    · exact map_zero _

theorem differentialJetMap_jet {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    (differentialJetMap f).comp (differentialJet R) = (differentialJet S).comp f.hom := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · rfl
  · exact DifferentialNaturality.differentialMap_D f r

theorem differentialJetMap_inl {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    (differentialJetMap f).comp (TrivSqZeroExt.inlAlgHom ℂ R (KaehlerDifferential ℂ R)) =
      (TrivSqZeroExt.inlAlgHom ℂ S (KaehlerDifferential ℂ S)).comp f.hom := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero _

theorem differentialJetMap_fst {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) :
    (TrivSqZeroExt.fstHom ℂ S (KaehlerDifferential ℂ S)).comp (differentialJetMap f) =
      f.hom.comp (TrivSqZeroExt.fstHom ℂ R (KaehlerDifferential ℂ R)) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.DifferentialJet
