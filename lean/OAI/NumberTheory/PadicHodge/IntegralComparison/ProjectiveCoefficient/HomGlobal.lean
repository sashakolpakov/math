import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BasisGluingNormalization

/-! # Hom Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomGlobal

noncomputable section

/-! Intrinsic finite-flat coefficient duality for the original
projective resolutions. The global isomorphism is glued from actual
coefficient evaluation on ordinary affine coordinate subopens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomLocal

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def Good (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) : Prop :=
  ∃ k : Fin (n + 1), U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k

omit [IsNoetherianRing R] in
theorem good_principal (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (h : Good U) (r : Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U)) :
    Good ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen r) :=
  ⟨h.choose, ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans h.choose_spec⟩

omit [IsNoetherianRing R] in
theorem exists_neighborhood (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (x : Projective.IntrinsicOverlap.Intrinsic.space R n) (hx : x ∈ U) :
    ∃ V, IsAffineOpen V ∧ Good V ∧ x ∈ V ∧ V ≤ U := by
  have hcover : x ∈ ⨆ k : Fin (n + 1), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨k, hxk⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Projective.IntrinsicOverlap.Intrinsic.space R n).isBasis_affineOpens (show x ∈ U ⊓ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k from ⟨hx, hxk⟩)
  exact ⟨V, hV, ⟨k, hVU.trans inf_le_right⟩, hxV, hVU.trans inf_le_left⟩

variable (X : Over (Spec (CommRingCat.of R))) {Y : Scheme.{u}}
  (f : Y ⟶ X.left) [IsFinite f] [Flat f]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R n) [IsClosedImmersion i.left]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom] [IsProper X.hom]
  (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n)

def chosenSectionIso (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U) (h : Good U) :=
  HomLocal.sectionIso X f i g j B hB hg U hU h.choose h.choose_spec

theorem chosen_principal (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U) (h : Good U)
    (r : Γ(Projective.IntrinsicOverlap.Intrinsic.space R n, U)) (z : Γ(HomLocal.sourceSheaf X f i g j B, U)) :
    (chosenSectionIso X f i g j B hB hg ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen r) (hU.basicOpen r)
        (good_principal U h r)).hom
      ((HomLocal.sourceSheaf X f i g j B).presheaf.map (homOfLE ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op z) =
    (HomLocal.targetSheaf X f i g).presheaf.map (homOfLE ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r)).op
      ((chosenSectionIso X f i g j B hB hg U hU h).hom z) := by
  rw [chosenSectionIso, HomRestriction.independent X f i g j B hB hg
    ((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen r) (hU.basicOpen r) _ _ h.choose
    (((Projective.IntrinsicOverlap.Intrinsic.space R n).basicOpen_le r).trans h.choose_spec)]
  exact HomRestriction.restriction X f i g j B hB hg U hU
    h.choose h.choose_spec r z

def iso : HomLocal.sourceSheaf X f i g j B ≅ HomLocal.targetSheaf X f i g :=
  Principal.BasisGluing.iso (HomLocal.sourceSheaf X f i g j B) (HomLocal.targetSheaf X f i g) Good
    (fun U hU h => (chosenSectionIso X f i g j B hB hg U hU h).hom.hom)
    (fun U _ h r => good_principal U h r)
    (chosen_principal X f i g j B hB hg) exists_neighborhood
    (fun U hU h => ConcreteCategory.bijective_of_isIso
      (chosenSectionIso X f i g j B hB hg U hU h).hom)

theorem iso_app (U : (Projective.IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U) (h : Good U)
    (z : Γ(HomLocal.sourceSheaf X f i g j B, U)) :
    (iso X f i g j B hB hg).hom.app U z =
      (chosenSectionIso X f i g j B hB hg U hU h).hom z :=
  Principal.BasisGluingNormalization.iso_app (HomLocal.sourceSheaf X f i g j B) (HomLocal.targetSheaf X f i g) Good
    (fun U hU h => (chosenSectionIso X f i g j B hB hg U hU h).hom.hom)
    (fun U _ h r => good_principal U h r)
    (chosen_principal X f i g j B hB hg) exists_neighborhood
    (fun U hU h => ConcreteCategory.bijective_of_isIso
      (chosenSectionIso X f i g j B hB hg U hU h).hom) U hU h z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.HomGlobal
