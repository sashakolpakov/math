import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.TorRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor

/-! # Pullback Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackEuler

noncomputable section

/-! One-sided smooth base change for the actual support Tor Euler
characteristic, with the native residue-degree weight. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem congr (R : Type) [CommRing R] {M M' N N' : ModuleCat R}
    (eM : M ≅ M') (eN : N ≅ N') (d : ℕ) :
    Tor.Euler.euler R M N d = Tor.Euler.euler R M' N' d := by
  unfold Tor.Euler.euler ExactLength.rationalLength
  simp_rw [Open.SupportTor.length_iso R eM eN]

theorem residue_length {X Y : Scheme} (f : X ⟶ Y) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    letI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := f.toLRSHom.prop x
    (Module.length (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).toNat = f.residueDegree x := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := f.toLRSHom.prop x
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  change Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) = _
  unfold Scheme.Hom.residueDegree
  apply @Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ inferInstance
    (Y.residueField (f x)) (X.residueField x) _ _ (f.residueFieldMap x).hom.toAlgebra
    (RingEquiv.refl _) (RingEquiv.refl _)
  ext t
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective t
  rfl

theorem euler {X Y : Scheme} [IsLocallyNoetherian Y] (f : X ⟶ Y) [Smooth f]
    [GeometricallyIntegral f] (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : f x ∈ (B : Set Y)) (d : ℕ) :
    Tor.Euler.euler (Y.presheaf.stalk (f x)) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B (f x) hxB)
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hxA)) d =
    Tor.Euler.euler (X.presheaf.stalk x)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f B) x (PullbackModule.mem f B x hxB))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hxA) d * (f.residueDegree x : ℚ) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : Module.Flat R S := Flat.stalkMap f x
  let : IsLocalHom (algebraMap R S) := f.toLRSHom.prop x
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hxA
  let : Module R N := Module.compHom N (algebraMap R S)
  let : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  have h := Tor.TorRestriction.euler R S N (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B (f x) hxB) d
  rw [residue_length f x] at h
  exact h.trans (congrArg (fun a : ℚ => a * (f.residueDegree x : ℚ))
    (congr S (PullbackModule.equiv f B x hxB).toModuleIso (Iso.refl N) d))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackEuler
