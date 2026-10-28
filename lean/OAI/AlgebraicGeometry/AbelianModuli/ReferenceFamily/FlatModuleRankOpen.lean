import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Flat Module Rank Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FlatModuleRankOpen

noncomputable section

/-! The geometric rank of a finitely presented flat module is represented
by its actual clopen rank locus on every test scheme. No reducedness or
finiteness condition is imposed on the tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type} [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
  [Module.Flat R V] [Module.FinitePresentation R V]

def flatModuleRankOpen (r : ℕ) : (Spec (.of R)).Opens :=
  ⟨{p | Module.rankAtStalk (R := R) V p = r},
    (Module.isLocallyConstant_rankAtStalk (R := R) (M := V)).isOpen_fiber r⟩

theorem flatModuleRankOpen_isClosed (r : ℕ) :
    IsClosed (flatModuleRankOpen (R := R) V r : Set (Spec (.of R))) :=
  (Module.isLocallyConstant_rankAtStalk (R := R) (M := V)).isClopen_fiber r |>.1

theorem flatModule_field_fiber_rank {k : Type} [Field k] (f : Spec (.of k) ⟶ Spec (.of R)) :
    letI : Algebra R k := (Spec.preimage f).hom.toAlgebra
    Module.finrank k (k ⊗[R] V) =
      Module.rankAtStalk (R := R) V (f (IsLocalRing.closedPoint k)) := by
  let φ := (Spec.preimage f).hom
  let : Algebra R k := φ.toAlgebra
  have h := Module.rankAtStalk_baseChange (R := R) (M := V) (S := k) (IsLocalRing.closedPoint k)
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  have he : Spec.map (CommRingCat.ofHom φ) = f := Spec.map_preimage f
  exact h.trans (congrArg (Module.rankAtStalk (R := R) V)
    (congrArg (fun q : Spec (.of k) ⟶ Spec (.of R) => q (IsLocalRing.closedPoint k)) he))

theorem flatModuleRankOpen_classifies (r : ℕ) {T : Scheme.{0}} (f : T ⟶ Spec (.of R)) :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
      letI : Algebra R k := (Spec.preimage (p ≫ f)).hom.toAlgebra
      Module.finrank k (k ⊗[R] V) = r) ↔
        ∃! q : T ⟶ (flatModuleRankOpen (R := R) V r).toScheme,
          q ≫ (flatModuleRankOpen (R := R) V r).ι = f := by
  let U := flatModuleRankOpen (R := R) V r
  constructor
  · intro h
    have hrange : Set.range f ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      let k := AlgebraicClosure (T.residueField t)
      let p : Spec (.of k) ⟶ T :=
        Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) k)) ≫ T.fromSpecResidueField t
      have hp : p (IsLocalRing.closedPoint k) = t := T.fromSpecResidueField_apply t _
      have hr := (flatModule_field_fiber_rank V (p ≫ f)).symm.trans (h k p)
      change Module.rankAtStalk (R := R) V (f t) = r
      change Module.rankAtStalk (R := R) V (f (p (IsLocalRing.closedPoint k))) = r at hr
      rw [hp] at hr
      exact hr
    let q := IsOpenImmersion.lift U.ι f hrange
    have hq : q ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
    exact ⟨q, hq, fun v hv => (cancel_mono U.ι).mp (hv.trans hq.symm)⟩
  · rintro ⟨q, hq, _⟩ k _ _ p
    apply (flatModule_field_fiber_rank V (p ≫ f)).trans
    have he : f (p (IsLocalRing.closedPoint k)) = (q (p (IsLocalRing.closedPoint k))).val :=
      (congrArg (fun m : T ⟶ Spec (.of R) => m (p (IsLocalRing.closedPoint k))) hq).symm
    change Module.rankAtStalk (R := R) V (f (p (IsLocalRing.closedPoint k))) = r
    rw [he]
    exact (q (p (IsLocalRing.closedPoint k))).property

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FlatModuleRankOpen
