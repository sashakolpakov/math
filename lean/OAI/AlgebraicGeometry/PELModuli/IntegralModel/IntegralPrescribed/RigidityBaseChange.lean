import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.Freeness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.ScalarChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent

/-! # Rigidity Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityBaseChange

noncomputable section

/-! A uniform arithmetic rigidity coefficient becomes prescribed-level
rigidity of the actual base-changed two-level family once it is a unit. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ}
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* R}
    {X : Over (Spec (.of R))}

theorem integralAddedPEL_prescribedRigid_baseChange_of_away
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (r : R)
    (hrigid : ∀ (T : Over X.left) [IsReduced T.left]
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (U.forgetAuxiliary.data.polarized.pullback T.hom)
        (U.forgetAuxiliary.data.polarized.pullback T.hom)),
      (∀ x : T.left, r ∉ (X.hom (T.hom x)).asIdeal) →
      e.abelian.hom = 𝟙 (U.forgetAuxiliary.data.polarized.abelian.pullback T.hom).scheme)
    (φ : R →+* R') (hr : IsUnit (φ r)) : (U.baseChange φ).PrescribedRigid := by
  intro T _ f e
  let b := Spec.map (CommRingCat.ofHom φ)
  let q := pullback.fst X.hom b
  let t := f.left ≫ q
  have : IsReduced (Over.mk t).left := inferInstanceAs (IsReduced T.left)
  apply AbelianModuli.ReferenceFamily.Pure.AutomorphismDescent.pure_abelian_eq_id_via e
    (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp U.forgetAuxiliary.data.polarized q f.left)
  intro a
  apply hrigid (Over.mk t) a
  intro x hx
  have hb : t ≫ X.hom = T.hom ≫ b := by
    change (f.left ≫ pullback.fst X.hom b) ≫ X.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun a => a ≫ b) f.w
  have hp : X.hom (t x) = b (T.hom x) := congrArg (fun a : T.left ⟶ Spec (.of R) => a x) hb
  have hx' : φ r ∈ (T.hom x).asIdeal :=
    (congrArg (fun z : Spec (.of R) => r ∈ z.asIdeal) hp).mp hx
  exact (T.hom x).isPrime.ne_top ((T.hom x).asIdeal.eq_top_of_isUnit_mem hx' hr)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityBaseChange
