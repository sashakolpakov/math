import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLabelTransport

/-! # Etale Line Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineTransport.Construction

noncomputable section

/-!
The line permutation induced by a native active-plane isomorphism
transports the original embedded line group schemes. The comparison is
an equality of native morphisms, verified on all test schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable (q : ℕ) [Fact q.Prime]

def liftedActiveEtaleLinearIso
    (a : EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q) :
    ULift.{u} (Multiplicative (EtaleSubgroups.Construction.ActiveEtalePlane q)) ≃*
      ULift.{u} (Multiplicative (EtaleSubgroups.Construction.ActiveEtalePlane q)) :=
  (MulEquiv.ulift.trans (AddEquiv.toMultiplicative a.toAddEquiv)).trans MulEquiv.ulift.symm

/-- Restrict the induced linear map to each actual source line. -/
def activeEtaleLineRestriction
    (a : EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    L.val ≃ₗ[ZMod q] (EtaleLabelTransport.Construction.activeEtaleLineEquiv q a L).val :=
  a.submoduleMap L.val

def liftedActiveEtaleLineRestriction
    (a : EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    ULift.{u} (Multiplicative L.val) ≃*
      ULift.{u} (Multiplicative (EtaleLabelTransport.Construction.activeEtaleLineEquiv q a L).val) :=
  (MulEquiv.ulift.trans
    (AddEquiv.toMultiplicative (activeEtaleLineRestriction q a L).toAddEquiv)).trans
      MulEquiv.ulift.symm

/-- The corresponding native isomorphism between the embedded line
schemes is constructed from the actual restricted label map. -/
def activeEtaleLineSchemeIso (S : Scheme.{u})
    (a : EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    EtaleSubgroups.Construction.activeEtaleLineScheme S q L ≅ EtaleSubgroups.Construction.activeEtaleLineScheme S q (EtaleLabelTransport.Construction.activeEtaleLineEquiv q a L) :=
  EtaleGroupFunctor.Construction.etaleGroupIso S (liftedActiveEtaleLineRestriction q a L)

theorem activeEtaleLineSchemeIso_embedding (S : Scheme.{u})
    (a : EtaleSubgroups.Construction.ActiveEtalePlane q ≃ₗ[ZMod q] EtaleSubgroups.Construction.ActiveEtalePlane q) (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (activeEtaleLineSchemeIso q S a L).hom ≫
      EtaleSubgroups.Construction.activeEtaleLineEmbedding S q (EtaleLabelTransport.Construction.activeEtaleLineEquiv q a L) =
    EtaleSubgroups.Construction.activeEtaleLineEmbedding S q L ≫
      EtaleSubgroups.Construction.etaleGroupMap S (liftedActiveEtaleLinearIso q a).toMonoidHom := by
  change EtaleSubgroups.Construction.etaleGroupMap S (liftedActiveEtaleLineRestriction q a L).toMonoidHom ≫
      EtaleSubgroups.Construction.etaleGroupMap S (EtaleSubgroups.Construction.liftedActiveEtaleLineLabels q (EtaleLabelTransport.Construction.activeEtaleLineEquiv q a L)) =
    EtaleSubgroups.Construction.etaleGroupMap S (EtaleSubgroups.Construction.liftedActiveEtaleLineLabels q L) ≫
      EtaleSubgroups.Construction.etaleGroupMap S (liftedActiveEtaleLinearIso q a).toMonoidHom
  rw [EtaleGroupFunctor.Construction.etaleGroupMap_comp, EtaleGroupFunctor.Construction.etaleGroupMap_comp]
  congr 1

theorem liftedActiveEtaleLinearIso_native (k : Type u) [Field k]
    (a : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q) :
    liftedActiveEtaleLinearIso q (EtaleLabelTransport.Construction.activeEtaleLinearEquiv q k a) = EtaleLabelTransport.Construction.fieldEtaleLabelIso k a := by
  apply MulEquiv.ext
  intro x
  rfl

/-- Each original native active line is transported to the line in the
derived permutation, with its original inclusion square. -/
theorem nativeActiveEtaleLineIso_embedding (k : Type u) [Field k]
    (a : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ≅ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q)
    (L : EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (activeEtaleLineSchemeIso q (Spec (.of k)) (EtaleLabelTransport.Construction.activeEtaleLinearEquiv q k a) L).hom ≫
      EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q (EtaleLabelTransport.Construction.nativeActiveEtaleLineEquiv q k a L) =
    EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L ≫ a.hom := by
  have h := activeEtaleLineSchemeIso_embedding q (Spec (.of k)) (EtaleLabelTransport.Construction.activeEtaleLinearEquiv q k a) L
  rw [liftedActiveEtaleLinearIso_native] at h
  exact h.trans (congrArg
    (fun z : EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q ⟶ EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q =>
      EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L ≫ z)
    (EtaleLabelTransport.Construction.fieldEtaleLabelIso_recovers k a).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineTransport.Construction
