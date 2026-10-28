import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PrescribedRanks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters

/-! # Lie Signature -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature

noncomputable section

/-! The original reference action has TateComparison's literal geometric
Lie signature, including its base-ring action on global sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters

theorem integralAction_ext {R : Type} [CommRing R] {S : Scheme} {g : ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {ρ σ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A}
    (h : ∀ a, ρ.map a = σ.map a) : ρ = σ := by
  cases ρ
  cases σ
  congr
  exact funext h

theorem actionFromEnd_baseChange {R : Type} [CommRing R] {S T : Scheme} {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (a : R →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.scheme) (t : T ⟶ S) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange A.scheme t).comp a) = (AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd a).pullback t := by
  apply integralAction_ext
  intro r
  exact AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap A.scheme t (a r)

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

def referenceComplexBaseAction (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) :
    NumberField.RingOfIntegers E →+* Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) :=
  (Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp
    (P.μ.comp (algebraMap (NumberField.RingOfIntegers E) E))

theorem reference_geometric_lie_signature
    (k : Type) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (τ : E ≃ₐ[ℚ] E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (M.abelianScheme.pullback t)
      (AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange M.abelianScheme.scheme t).comp M.functorAction))
      (((Scheme.ΓSpecIso (.of k)).hom.hom.comp (t.appTop.hom.comp (referenceComplexBaseAction P))).comp
        (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom) (P.lieRank τ) := by
  let j : ℂ →+* k := (Spec.preimage t).hom
  have ht : Spec.map (CommRingCat.ofHom j) = t := Spec.map_preimage t
  let : Algebra ℂ k := j.toAlgebra
  have hr := M.hasGeometricLieRank k τ
  have hbase : LieFieldTests.fieldBaseMap ℂ k = t := ht
  rw [hbase] at hr
  have haction : AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters.actionFromEnd ((AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange.endBaseChange M.abelianScheme.scheme t).comp M.functorAction) =
      M.integralAction.pullback t := actionFromEnd_baseChange M.abelianScheme M.functorAction t
  rw [haction]
  have hchar :
      ((Scheme.ΓSpecIso (.of k)).hom.hom.comp (t.appTop.hom.comp (referenceComplexBaseAction P))).comp
        (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.geometricCharacter k (P.μ.comp τ.toRingHom) := by
    apply RingHom.ext
    intro a
    have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j))
      ((Scheme.ΓSpecIso (.of ℂ)).inv (P.μ (τ (a : E))))
    rw [ht] at hn
    change (Scheme.ΓSpecIso (.of k)).hom
      (t.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv (P.μ (τ (a : E))))) = j (P.μ (τ (a : E)))
    exact hn.trans (congrArg j
      ((Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.apply_symm_apply _))
  rw [hchar]
  exact hr

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.LieSignature
