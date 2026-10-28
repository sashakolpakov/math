import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Relation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrbitQuotientExists
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleKernelPair
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Quotient.IntegralAuxiliaryAction

noncomputable section

/-! Construct the reduced finite etale quotient of the actual integral
auxiliary relation whenever its finite orbits have affine neighborhoods.
No quotient scheme or effectiveness witness is an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem exists_quotient_scheme (hrigid : U.PrescribedRigid)
    (hOrbit : ∀ x : X.left, ∃ V : X.left.Opens, IsAffineOpen V ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left x y → y ∈ V) :
    ∃ (Q : Scheme.{0}) (π : X.left ⟶ Q), IsReduced Q ∧
      IsFinite π ∧ Etale π ∧ Surjective π ∧
      IsKernelPair π (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left ∧
      ∀ (T : Scheme.{0}) (f : X.left ⟶ T),
        (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left ≫ f = (ActionSpace.IntegralAuxiliaryAction.target U hU).left ≫ f →
        ∃! q : Q ⟶ T, π ≫ q = f := by
  let H := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R)) (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)
  let e := Relation.IntegralAuxiliaryAction.equivalenceRelation U hU hrigid
  obtain ⟨Q, π, hf, hflat, hfp, hs, hk, hq⟩ := Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient.exists_quotient
    H.hom X.hom (prod.snd : ActionSpace.IntegralAuxiliaryAction.relation X (3 * s) L ⟶ H).left
    (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (ActionSpace.IntegralAuxiliaryAction.target U hU).left (ActionSpace.IntegralAuxiliaryAction.source_isPullback X (3 * s) L)
    e ((ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).w.trans (ActionSpace.IntegralAuxiliaryAction.target U hU).w.symm) hOrbit
  have : IsFinite π := hf
  have : Flat π := hflat
  have : LocallyOfFinitePresentation π := hfp
  have : Surjective π := hs
  exact ⟨Q, π, Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_finite_flat_surjective π, hf,
    AbelianModuli.ReferenceFamily.EtaleKernelPair.etale_of_etale_kernelPair _ _ π e hk, hs, hk, hq⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Quotient.IntegralAuxiliaryAction
